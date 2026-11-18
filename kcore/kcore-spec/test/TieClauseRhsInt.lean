/-
  The fixture e2-clause-rhs-int: `rule f() => c(Y:Int) [unboundVariables(Y)]` (`T ::= c(Int)`,
  `T ::= f() [function]`). The text is `f2-examples/rhsint.kompile.kore`, the kompiled text of
  `test/constructs/fixtures/e2-clause-rhs-int`; its sentence 205 is `f() = c(Y)` with Y free, so
  universal over Int, 78 states that `c` is functional and 79 that it is injective (no confusion
  of one constructor); sentence numbers are `AxiomDecl.index`, the text's axioms counted from 1.
  Run from the package root: `lake env lean -j1 test/TieClauseRhsInt.lean`. Every statement is on
  the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  - Function equations (`fnText`: sentence 205, then the sort predicates'): each of Γ's items is the
    translation of its sentence (`shape`), so Γ entails each (`fns_entailed`). Sentences 78 and 79
    are constructor sentences Γ's constructor items entail (`cons_entailed`).
  - The text has no model (C7 form (r)). At Y = 0 and at Y = 1 the equation gives `f()` the element
    of `c(0)` and that of `c(1)` (`KCore.clause_two_elems`, the core of `KCore.clause_two_instances`); by Γ's constructor item of `c`'s
    injectivity (what 79 states) the two would have one argument element, and two distinct Int
    literals denote distinct elements (ΓDomains; no sentence of the text states `0 ≠ 1`). So Γ has no
    model (`gamma_no_model`), nor has `Pre`, the premise set form (a) would use (the function
    sentences as written, Γ's rule items, the families: `no_model`), nor the reading's theory with
    the step's closure (`inconsistent`).
  - The fact the package names as owed for the clause (`matchObligationsL`), its `MatchIndependent`,
    is false: Y = 0 and Y = 1 both decide `f()`, with the results `c(0)` and `c(1)`
    (`owed_refuted`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieClauseRhsInt

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rhsint.kompile.kore"
definition_of defn from "f2-examples/rhsint.kompile.kore"
user_axioms U from "f2-examples/rhsint.kompile.kore" module "E2-CLAUSE-RHS-INT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## What the reader reads -/

def fS : Sym := 386
def cS : Sym := 385
def tS : Srt := 32

/-- The symbols and the sort the clause names. -/
theorem names : c.symName fS = "Lblf" ∧ c.symName cS = "Lblc" ∧ c.sortName tS = "T" := by
  decide +kernel

/-- The semantics is `coreOK` and `rightValued`; the one function is `f`, and the fact owed of its
clause is match independence (`matchObligationsL`); no rule and no clause owes a condition. -/
theorem named : c.coreOK = true ∧ c.rightValued = true ∧ (c.fns.map (·.label)) = [fS] ∧
    c.matchObligationsL = [(fS, 0)] ∧ c.owedRules = [] ∧ c.owedClauses = [] := by
  decide_cheap

theorem coreOK : c.coreOK = true := named.1
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem sortOfH (H : HookParams) : (cH H).sortOf = c.sortOf := Semantics.sortOf_withHooks c H noRaw
theorem sortsOfH (H : HookParams) : (cH H).sortsOf = c.sortsOf := Semantics.sortsOf_withHooks c H noRaw

/-- The parts of the semantics read below do not read the hook interpretation. -/
theorem wh_patCtxAll (d : Semantics) (H : HookParams) : (d.withHooks H).patCtxAll = d.patCtxAll := rfl
theorem wh_isCtor (d : Semantics) (H : HookParams) : (d.withHooks H).isCtor = d.isCtor := rfl
theorem wh_ctorSigs (d : Semantics) (H : HookParams) : (d.withHooks H).ctorSigs = d.ctorSigs := rfl
theorem wh_consSorts (d : Semantics) (H : HookParams) : consSorts (d.withHooks H) = consSorts d := rfl
theorem wh_gens (d : Semantics) (H : HookParams) : (d.withHooks H).gens = d.gens := rfl
theorem wh_isOpenGen (d : Semantics) (H : HookParams) : (d.withHooks H).isOpenGen = d.isOpenGen := rfl
theorem wh_fnOvl (d : Semantics) (H : HookParams) : (d.withHooks H).fnOvl = d.fnOvl := rfl

/-! ## The sentences -/

/-- The text sentences of Γ's equations, in `fnItems`'s order: `f`'s one (205, `f() = c(Y)`),
then the sort predicates' (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := [U.ax205] ++ (TiePair.fnTextOf c U.all).drop 1

theorem fnText_head : (fnText.map (·.index)).head? = some 205 := by decide +kernel

/-- The translations of the text's sentences, in that order. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence**, pattern for pattern or with
one variable renamed (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for the function equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun ad had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

/-- Sentences 78 (`c` functional) and 79 (`c` injective) are the constructor sentences of `c`,
which read no declaration and no alias. -/
theorem cons_text : U.ax78.index = 78 ∧ U.ax79.index = 79 ∧ tieConsB c U.ax78.ax = true ∧
    tieConsB c U.ax79.ax = true ∧ (trS U.ax78).pat = (trAxiom [] [] U.ax78).pat ∧
    (trS U.ax79).pat = (trAxiom [] [] U.ax79).pat := by
  decide +kernel

/-- **E for the constructor sentences of `c`**: Γ entails 78 and 79, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ [U.ax78, U.ax79], Γ (cH H) ⊧ (trS ad).pat := by
  obtain ⟨-, -, h78, h79, t78, t79⟩ := cons_text
  intro _ad had M _ I hI
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl
  · rw [t78]
    exact tieCons_entailed (c := cH H) (a := U.ax78.ax) ((tieConsB_withHooks c H _).trans h78) _ _ hI
  · rw [t79]
    exact tieCons_entailed (c := cH H) (a := U.ax79.ax) ((tieConsB_withHooks c H _).trans h79) _ _ hI

/-! ## The function and its clause -/

noncomputable def fF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def clY : Clause := fF.clauses[0]'(by decide +kernel)

theorem fF_mem : fF ∈ c.fns := List.getElem_mem _

/-- `f() => c(Y:Int)`: no argument, one clause, one variable (of Int) its patterns do not bind, no
`requires` or `ensures`, no existential variable. -/
theorem fF_shape : fF.label = fS ∧ fF.args = [] ∧ fF.result = tS ∧ fF.clauses.length = 1 ∧
    clY.vars = [Srt.int] ∧ clY.pats.isEmpty = true ∧ clY.req.isNone = true ∧ clY.ens.isNone = true ∧
    clY.exs = [] ∧ c.isCtor cS = true ∧ lookupSig c.ctorSigs cS = some ⟨cS, [Srt.int], tS⟩ := by
  decide +kernel

theorem clY_rhs : clY.rhs = .app cS [.var 0] := by rfl
theorem clY_pre : clY.pre = .top := by rfl
theorem clY_pats : clY.pats = [] := List.isEmpty_iff.mp fF_shape.2.2.2.2.2.1
theorem clY_req : clY.req = none := Option.isNone_iff_eq_none.mp fF_shape.2.2.2.2.2.2.1
theorem clY_ens : clY.ens = none := Option.isNone_iff_eq_none.mp fF_shape.2.2.2.2.2.2.2.1

theorem clauses_eq : fF.clauses = [clY] := by
  apply List.ext_getElem (by rw [fF_shape.2.2.2.1]; rfl)
  intro i h1 _
  have : i < 1 := fF_shape.2.2.2.1 ▸ h1
  match i, this with
  | 0, _ => rfl

theorem lookupF : c.lookupFn fS = some fF := fF_shape.1 ▸ lookupFn_of_core coreOK fF_mem
theorem lookupFH (H : HookParams) : (cH H).lookupFn fS = some fF := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF

theorem lookupFH_eq {H : HookParams} {fn : Fn} (h : (cH H).lookupFn fS = some fn) : fn = fF :=
  Option.some.inj (h.symm.trans (lookupFH H))

/-! ## Two instances: Y = 0 and Y = 1 -/

/-- The substitution `Y ↦ n`. -/
def σn (n : Int) : Subst := [(0, .dv Srt.int (.int n))]

/-- The value `c(n)`. -/
def vn (n : Int) : GroundTerm := .ctor cS [.dv Srt.int (.int n)]

theorem int_sort (n : Int) : c.sortOf (.dv Srt.int (.int n)) = some Srt.int := by
  simp [Semantics.sortOf, show dvOK c.lib Srt.int (.int n) = true from rfl]

theorem ws_n (H : HookParams) (n : Int) : (cH H).WellSorted clY.vars (σn n) := fun i s hs => by
  rw [fF_shape.2.2.2.2.1] at hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨_, rfl, by rw [sortOfH]; exact int_sort n⟩
  | succ i => simp at hs

theorem vn_sort (H : HookParams) (n : Int) : (cH H).sortOf (vn n) = some fF.result := by
  rw [sortOfH, fF_shape.2.2.1]
  unfold vn
  exact sortOf_ctor_intro ⟨_, fF_shape.2.2.2.2.2.2.2.2.2.2, sortsOf_cons.mpr ⟨_, _, int_sort n, sortsOf_nil, rfl⟩, rfl⟩

/-- `c(Y)` under `Y ↦ n` is the value `c(n)`. -/
theorem patval (H : HookParams) (n : Int) : PatVal (cH H) (σn n) clY.rhs (vn n) := by
  rw [clY_rhs]
  exact .ctor (by rw [wh_isCtor]; exact fF_shape.2.2.2.2.2.2.2.2.2.1) (.cons (.var rfl) .nil)

/-- The constructor `c : Int → T`. -/
def kc : CtorSig := ⟨cS, [Srt.int], tS⟩

theorem lowY : lowerClauses fF clY = [] := List.isEmpty_iff.mp (by decide +kernel)
theorem clY_post : clY.post = .top := by rfl
theorem rhsv : ∀ i ∈ varOccs clY.rhs, i < clY.vars.length := by
  rw [clY_rhs, fF_shape.2.2.2.2.1]; simp [varOccs, varOccsList]

/-- `c`'s sort `T` is a constructor sort, `c` one of its generators, and no overload bears `c`'s
name. -/
theorem consT : tS ∈ consSorts c := by decide +kernel
theorem kc_mem : kc ∈ c.ctorSigs := by
  have h := fF_shape.2.2.2.2.2.2.2.2.2.2
  rw [lookupSig_eq] at h
  exact List.mem_of_find?_eq_some h
theorem gensT : Gen.ctor kc ∈ (c.gens tS).filter (!c.isOpenGen ·) :=
  List.mem_filter.mpr ⟨gens_ctor kc_mem, by
    show (!(c.lookupOpen kc.name).isSome) = true
    rw [c.lookupOpen_of_noRaw noRaw]; rfl⟩
theorem fnOvlT : c.fnOvl (.ctor kc) = false := by decide +kernel
theorem consTH (H : HookParams) : tS ∈ consSorts (cH H) := by rw [wh_consSorts]; exact consT
theorem gensTH (H : HookParams) : Gen.ctor kc ∈ ((cH H).gens tS).filter (!(cH H).isOpenGen ·) := by
  rw [wh_gens, wh_isOpenGen]; exact gensT
theorem fnOvlTH (H : HookParams) : (cH H).fnOvl (.ctor kc) = false := by rw [wh_fnOvl]; exact fnOvlT

theorem rhs_sort : sortOfTerm c.patCtxAll clY.vars clY.rhs = some fF.result := by decide +kernel
theorem rhs_plainH (H : HookParams) : plainPat (cH H) clY.rhs = true := by
  rw [clY_rhs, plainPat, plainPats, plainPat, plainPats, wh_isCtor, fF_shape.2.2.2.2.2.2.2.2.2.1]
  decide
theorem rhs_sortH (H : HookParams) : sortOfTerm (cH H).patCtxAll clY.vars clY.rhs = some fF.result := by
  rw [wh_patCtxAll]; exact rhs_sort
theorem pats_sorts : sortsOfTerms c.patCtxAll clY.vars clY.pats = some fF.args := by
  rw [clY_pats, fF_shape.2.1]; rfl

/-- Each variable of the clause occurs in it: Y in the right side. -/
theorem occ : ∀ i < clY.vars.length, i ∈ varOccsList clY.pats ++ clY.condVars ++ varOccs clY.rhs ++
    (clY.ens.map varOccs).getD [] := by
  intro i hi
  rw [fF_shape.2.2.2.2.1] at hi
  have : i = 0 := by simpa using hi
  subst this
  rw [clY_rhs]
  simp [varOccs, varOccsList]

/-- **Sentence 205 at Y = 0 and at Y = 1**: in a model of Γ, for every H, `c(0)` and `c(1)` denote
one element, `f()`'s (`clause_two_elems`). -/
theorem two_elems (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hΓ : I ⊧ᴵP Γ (cH H)) : elemOf (cH H) I (vn 0) = elemOf (cH H) I (vn 1) := by
  obtain ⟨hsok, hsr', hnn, -, -, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have hfnm := (lookupFn_spec (lookupFH H)).1
  have ihrhs : ∀ n : Int, ∀ (tbl : VarTable) (e : Valuation M),
      Agrees (cH H) I tbl (canonVars (cH H) clY.vars) (σn n) e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight (cH H) fF clY)).interpret I e m ↔ Res (cH H) I e (some (vn n)) m :=
    fun n tbl e hag => right_iff hΓ hnn hfnm (fun v hv => by cases hv; exact vn_sort H n)
      (fun m => (patVal_den hΓ hnn.1 htr (ws_n H n) (canonVars_length _ _) hag (patval H n) (rhs_plainH H)
        (rhs_sortH H)).2 m)
      (fun t h => by rw [clY_ens] at h; cases h)
  have hmem : clY ∈ fF.clauses := by rw [clauses_eq]; exact List.mem_singleton_self _
  have hws : (cH H).sortsOf [] = some fF.args := by rw [fF_shape.2.1]; rfl
  have hpl : plainPats (cH H) clY.pats = true := by rw [clY_pats]; rfl
  have hps : sortsOfTerms (cH H).patCtxAll clY.vars clY.pats = some fF.args := by
    rw [wh_patCtxAll]; exact pats_sorts
  have hm : ∀ n : Int, PatVals (cH H) (σn n) clY.pats [] := fun n => by rw [clY_pats]; exact .nil
  have hreq : ∀ n : Int, ∀ (tbl : VarTable) (e : Valuation M),
      Agrees (cH H) I tbl (canonVars (cH H) clY.vars) (σn n) e → ∀ t, clY.req = some t → ∀ m,
        (KoreAML.tr ⟨tbl, []⟩ (Term.kore (cH H) (canonVars (cH H) clY.vars) t)).interpret I e m ↔
          (den (cH H) (bool true)).interpret I e m := fun _ _ _ _ t h => by rw [clY_req] at h; cases h
  exact clause_two_elems hΓ hnn htr (lookupFH H) hmem lowY clY_pre fF_shape.2.2.2.2.2.2.2.2.1 hws hpl hps occ
    (fun t h => by rw [clY_req] at h; cases h) rhsv (fun t h => by rw [clY_ens] at h; cases h)
    (ws_n H 0) (ws_n H 1) (hm 0) (hm 1) (vn_sort H 0) (vn_sort H 1) (hreq 0) (hreq 1) (ihrhs 0) (ihrhs 1)

theorem wh_genWf (d : Semantics) (H : HookParams) : genWf (d.withHooks H) = genWf d := rfl
theorem genWfC : genWf c = true := by decide +kernel

/-- **`KCore.clause_two_instances` at this text**: Γ has no model, for every H, from sentence 205
at Y = 0 and Y = 1 with the values `c(0) ≠ c(1)` of T, an `apartSort` sort (`genWf`). Here the
distinct values are put apart by `values_apart`; `gamma_no_model` below goes through `c`'s
constructor items instead. -/
theorem two_instances (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hΓ : I ⊧ᴵP Γ (cH H)) : False := by
  have hg : genWf (cH H) = true := by rw [wh_genWf]; exact genWfC
  obtain ⟨hsok, hsr', hnn, -, -, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have hfnm := (lookupFn_spec (lookupFH H)).1
  have ihrhs : ∀ n : Int, ∀ (tbl : VarTable) (e : Valuation M),
      Agrees (cH H) I tbl (canonVars (cH H) clY.vars) (σn n) e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight (cH H) fF clY)).interpret I e m ↔ Res (cH H) I e (some (vn n)) m :=
    fun n tbl e hag => right_iff hΓ hnn hfnm (fun v hv => by cases hv; exact vn_sort H n)
      (fun m => (patVal_den hΓ hnn.1 htr (ws_n H n) (canonVars_length _ _) hag (patval H n) (rhs_plainH H)
        (rhs_sortH H)).2 m)
      (fun t h => by rw [clY_ens] at h; cases h)
  have hmem : clY ∈ fF.clauses := by rw [clauses_eq]; exact List.mem_singleton_self _
  have hws : (cH H).sortsOf [] = some fF.args := by rw [fF_shape.2.1]; rfl
  have hpl : plainPats (cH H) clY.pats = true := by rw [clY_pats]; rfl
  have hps : sortsOfTerms (cH H).patCtxAll clY.vars clY.pats = some fF.args := by
    rw [wh_patCtxAll]; exact pats_sorts
  have hm : ∀ n : Int, PatVals (cH H) (σn n) clY.pats [] := fun n => by rw [clY_pats]; exact .nil
  have hreq : ∀ n : Int, ∀ (tbl : VarTable) (e : Valuation M),
      Agrees (cH H) I tbl (canonVars (cH H) clY.vars) (σn n) e → ∀ t, clY.req = some t → ∀ m,
        (KoreAML.tr ⟨tbl, []⟩ (Term.kore (cH H) (canonVars (cH H) clY.vars) t)).interpret I e m ↔
          (den (cH H) (bool true)).interpret I e m := fun _ _ _ _ t h => by rw [clY_req] at h; cases h
  exact clause_two_instances hΓ hnn htr hg (lookupFH H) (apartSort_of_sorted hg (vn_sort H 0)) hmem lowY clY_pre fF_shape.2.2.2.2.2.2.2.2.1 hws hpl hps occ
    (fun t h => by rw [clY_req] at h; cases h) rhsv (fun t h => by rw [clY_ens] at h; cases h)
    (ws_n H 0) (ws_n H 1) (hm 0) (hm 1) (vn_sort H 0) (vn_sort H 1) (hreq 0) (hreq 1) (ihrhs 0) (ihrhs 1)
    (by decide)

theorem int_sortH (H : HookParams) (n : Int) : (cH H).sortOf (.dv Srt.int (.int n)) = some Srt.int := by
  rw [sortOfH]; exact int_sort n

theorem int_distinct (H : HookParams) : (distinctSorts (cH H)).contains Srt.int = true := by
  unfold distinctSorts
  exact List.contains_iff_mem.mpr (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_cons_self ..)))))

/-- **`c(0)` and `c(1)` are distinct elements** in a model of Γ, for every H: by Γ's constructor
item of `c`'s injectivity (Cons-Inj, what 79 states) their argument elements would be one, and
ΓDomains puts the distinct Int literals 0 and 1 apart. -/
theorem c_apart (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hΓ : I ⊧ᴵP Γ (cH H)) (he : elemOf (cH H) I (vn 0) = elemOf (cH H) I (vn 1)) : False := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hk : lookupSig (cH H).ctorSigs cS = some kc := by rw [wh_ctorSigs]; exact fF_shape.2.2.2.2.2.2.2.2.2.2
  have hws : ∀ n : Int, (cH H).sortsOf [.dv Srt.int (.int n)] = some kc.args := fun n =>
    sortsOf_cons.mpr ⟨_, _, int_sortH H n, sortsOf_nil, rfl⟩
  have hgs : ∀ n : Int, ∀ m, (den (cH H) (vn n)).interpret I KoreAML.val0 m ↔
      GS I ((cH H).sortName tS) (Gen.toK (cH H) (.ctor kc)) [elemOf (cH H) I (.dv Srt.int (.int n))] m :=
    fun n m => den_ctor_gs hΓ hk (hws n) KoreAML.val0 m
  have hel : ∀ n : Int, ∀ m, (den (cH H) (vn n)).interpret I KoreAML.val0 m ↔ m = elemOf (cH H) I (vn n) :=
    fun n => (elemOf_spec hΓ (vn_sort H n) KoreAML.val0).1
  have hargs : ∀ n : Int, ∀ (i : Nat) x s, [elemOf (cH H) I (.dv Srt.int (.int n))][i]? = some x →
      ((Gen.ctor kc).argSorts.map (cH H).sortName)[i]? = some s → InS I s x := fun n i x s h1 h2 => by
    cases i with
    | zero =>
      simp only [Gen.argSorts, kc, List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      subst h1 h2
      exact (inS_iff _).mp (elemOf_spec hΓ (int_sortH H n) KoreAML.val0).2
    | succ i => simp at h1
  have hxy := gen_inj hΓ (consTH H) (gensTH H) (by simp [Gen.argSorts, kc]) (fnOvlTH H) (by rfl) (by rfl)
    (hargs 0) (hargs 1) (fun m => by rw [← hgs 0 m, ← hgs 1 m, hel 0 m, hel 1 m, he])
  have hxy' : elemOf (cH H) I (.dv Srt.int (.int 0)) = elemOf (cH H) I (.dv Srt.int (.int 1)) :=
    (List.cons.inj hxy).1
  have h0 := elemOf_spec hΓ (int_sortH H 0) KoreAML.val0
  have h1 := elemOf_spec hΓ (int_sortH H 1) KoreAML.val0
  exact dom_apart hΓ (int_distinct H) (int_sortH H 0) (int_sortH H 1) (by decide)
    KoreAML.val0 (elemOf (cH H) I (.dv Srt.int (.int 0))) ⟨(h0.1 _).mpr rfl, (h1.1 _).mpr hxy'⟩

/-- **Γ has no model, for every H**: at Y = 0 and Y = 1 sentence 205's equation makes `f()` both
`c(0)` and `c(1)` (`two_elems`), which are distinct elements (`c_apart`). -/
theorem gamma_no_model (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hΓ : I ⊧ᴵP Γ (cH H)) : False :=
  c_apart H hΓ (two_elems H hΓ)

/-! ## No model (C7 form (r)) -/

/-- The premises form (a) would use: the function sentences as written (205 and the sort
predicates'), Γ's rule items, and the families (the parts of Γ no sentence states: the constructor
items, among them `c`'s, which 78 and 79 state, and the domain values, which put 0 and 1 apart). -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **The text's sentences have no model, for every H**: `Pre`, which holds sentence 205 as written,
has none. -/
theorem no_model (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Pre H := by
  rintro ⟨M, _, I, hI⟩
  exact gamma_no_model H fun φ hφ => TiePair.gamma_from (shapeH H) φ hφ hI

/-- **The reading has no model either, for every H**: `Γc` with the step's closure is inconsistent. -/
theorem inconsistent (H : HookParams) : ¬ Consistent (cH H) := by
  rintro ⟨M, _, I, hI⟩
  exact gamma_no_model H fun φ hφ => hI φ (Or.inl (Or.inl hφ))

/-! ## The owed fact, refuted -/

theorem c_ctor (H : HookParams) : (cH H).isCtor cS = true := by rw [wh_isCtor]; exact fF_shape.2.2.2.2.2.2.2.2.2.1

/-- `c(Y)` has one result under each σ: `c` is a constructor. -/
theorem hdet (H : HookParams) (σ : Subst) : HDet (cH H) σ clY.rhs := by
  rw [clY_rhs]
  intro u hu r r' h1 h2
  simp only [subterms, subtermsList, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · cases h1 with
    | ctor _ hts1 =>
      cases h2 with
      | ctor _ hts2 =>
        cases hts1 with
        | cons h1' hs1 =>
          cases hts2 with
          | cons h2' hs2 =>
            cases hs1; cases hs2
            rw [EvalTerm.var_inv h1', EvalTerm.var_inv h2']
      | hook h => rw [c_ctor] at h; cases h
      | param h => rw [c_ctor] at h; cases h
      | call h => rw [c_ctor] at h; cases h
      | callUndef h => rw [c_ctor] at h; cases h
      | ovl h => rw [c_ctor] at h; cases h
      | ovlFn h => rw [c_ctor] at h; cases h
    | hook h => rw [c_ctor] at h; cases h
    | param h => rw [c_ctor] at h; cases h
    | call h => rw [c_ctor] at h; cases h
    | callUndef h => rw [c_ctor] at h; cases h
    | ovl h => rw [c_ctor] at h; cases h
    | ovlFn h => rw [c_ctor] at h; cases h
  · rw [EvalTerm.var_inv h1, EvalTerm.var_inv h2]

theorem eval_c (H : HookParams) (n : Int) : EvalTerm (cH H) (σn n) clY.rhs (some (vn n)) := by
  rw [clY_rhs]
  exact EvalTerm.ctor (rs := [some (.dv Srt.int (.int n))]) (c_ctor H) (.cons .var .nil)

/-- **The fact owed of the clause is false, for every H**: `f() => c(Y)` is not match independent:
Y = 0 and Y = 1 both decide `f()`, with the results `c(0)` and `c(1)`. -/
theorem owed_refuted (H : HookParams) : ¬ MatchIndependent (cH H) clY := fun h => by
  have ha : ∀ n : Int, clY.AppliesAt (cH H) (σn n) [] :=
    fun n => ⟨(ws_n H n).at _, by rw [clY_pats]; exact .nil, (fun t h => by rw [clY_req] at h; cases h), by rw [clY_pre]; exact .top⟩
  have hdec : ∀ n : Int, clY.Decides (cH H) fF (σn n) [] := fun n =>
    ⟨ha n, fun cl' h _ hlt => by rw [clauses_eq, List.mem_singleton] at h; subst h; exact absurd hlt (Nat.lt_irrefl _)⟩
  rcases h.1 [] (σn 0) (σn 1) (ha 0) (ha 1) (fun t h => by rw [clY_req] at h; cases h) (fun _ _ => hdet H (σn 0))
      (fun _ t h => by rw [clY_ens] at h; cases h) (fun hne => absurd fF_shape.2.2.2.2.2.2.2.2.1 hne)
      ⟨fS, fF, lookupFH H, by rw [clauses_eq]; exact List.mem_singleton_self _,
        by rw [clauses_eq]; exact List.mem_singleton_self _, hdec 0, hdec 1⟩ with ⟨-, -, -, -, hv, -⟩ | hr
  · have := hv 0 (by rw [clY_rhs]; simp [varOccs, varOccsList])
    simp [σn] at this
  · have := hr _ _ (.inl ⟨fF_shape.2.2.2.2.2.2.2.2.1, .inl ⟨(fun t h => by rw [clY_ens] at h; cases h), by rw [clY_post]; exact .top, eval_c H 0⟩⟩)
      (.inl ⟨fF_shape.2.2.2.2.2.2.2.2.1, .inl ⟨(fun t h => by rw [clY_ens] at h; cases h), by rw [clY_post]; exact .top, eval_c H 1⟩⟩)
    simp [vn] at this

end KCore.TieClauseRhsInt

#check @KCore.TieClauseRhsInt.no_model
#check @KCore.TieClauseRhsInt.inconsistent
#check @KCore.TieClauseRhsInt.owed_refuted
#print axioms KCore.TieClauseRhsInt.shape
#print axioms KCore.TieClauseRhsInt.fns_entailed
#print axioms KCore.TieClauseRhsInt.cons_entailed
#print axioms KCore.TieClauseRhsInt.two_instances
#print axioms KCore.TieClauseRhsInt.no_model
#print axioms KCore.TieClauseRhsInt.inconsistent
#print axioms KCore.TieClauseRhsInt.owed_refuted
