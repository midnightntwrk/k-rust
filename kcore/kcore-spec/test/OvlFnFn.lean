/-
  An overload whose larger symbol is a function (CN-4b section 5, unit OVF), on clauses built by
  hand from the kompiled sentences of test/constructs/fixtures/e5-ovl-fn-fn (and its variant
  e5-ovl-fn-fn-owise), as the reading of CN-4b section 5 writes them. Run from the package root:
  `lake env lean -j1 test/OvlFnFn.lean`. Kernel-checked; nothing here reads the reader.

  The text: `Exp ::= Int | e`, `negExp : Exp → Exp` a function (`anywhere` in the text),
  `negInt : Int → Int` a total function with `negInt(I) = 0 -Int I`, the user equation
  `negExp(e #as G0) = G0`, and the symbol-overload sentence
  `negExp(inj{Int,Exp}(K0)) = inj{Int,Exp}(negInt(K0))`. The overload sentence is read as one
  clause of `negExp` (`ovlCl`): its pattern the injected variable, its right side the injected
  application, `aside := true` (no `[owise]` premise kompile writes negates it: fixture
  e5-ovl-fn-fn-owise) and `prio := 0` (nothing is below it, so `Eval.clause`'s `hprio` reads no
  clause and its equation in `Γ` carries no negated competitor).

  - `c` (e5-ovl-fn-fn): `coreOK` (decided in parts, `coreOK_c`), which the landed `clausesPlain`
    admits with the `aside` clause; `Eval negExp [inj 3] (some (inj -3))` by the `aside` clause
    (`eval_inj3`) and `Eval negExp [e] (some e)` by the user clause (`eval_e`); `FnHyp`
    (`fnHyp_c`, the deciders confirming every obligation: the two clauses of `negExp` meet at no
    argument), hence `ClausesAgree` of `negExp` (`agree_c`).
  - `cC`: a clause of priority 0 that is not `aside`, `negExp(X) => e`, beside the `aside` clause
    (`coreOK_cC`). Both apply at `inj 3` and are of one priority, so they compete and `ClausesAgree` reads the pair
    (`compete_reads`); here they disagree there, so `ClausesAgree` of `negExp` is false
    (`not_agree_C`) and `Eval` has two results (`not_fnDet_C`).
  - `cO` (e5-ovl-fn-fn-owise): the `[owise]` clause `negExp(_) => e` (priority 200), whose premise
    negates the user clause only (`coreOK_cO`). At `inj 3` the user clause fails, so the `[owise]` clause decides
    with `e` (`eval_owise_inj3`), and the `aside` clause with `inj -3` (`eval_ovl_inj3_O`): two
    results, not `FnDet` (`not_fnDet_O`).
  - The overload clause as `emit` writes it: the reader gives it priority 0 not written, `aside` and
    the second symbol `negInt` (`ClausePres.overload`); `emit` writes its attribute
    `symbol-overload{}(LblnegExp{}(), LblnegInt{}())` alone (`ovl_emit_attrs`), the text's
    attributes of the sentence (natively, `#guard`, on the sentence parsed).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OvlFnFn

/-! ## The configuration and the split decision of `coreOK` (as test/OvlFun.lean) -/

def cellCtors (kc : Srt) (kl : Sym) : List CtorSig :=
  [⟨topLabel, [kc, Srt.counter], Srt.top⟩, ⟨topFragLabel, [kc + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨kl, [Srt.k], kc⟩, ⟨kl + 1, [], kc + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts (kc : Srt) : List (Srt × Srt) := [(kc, kc + 1), (Srt.counter, Srt.counterOpt)]

def lib0 : Lib := { sortsBelowKItem := [Srt.int, Srt.bool], ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩] }

def intT (i : Int) : Term := .dv Srt.int (.int i)

/-- Every condition of `coreOK` but `overloadsOK`. -/
def others (c : Semantics) : Bool := c.sortedOK && c.faithCoreOK && c.predsApart && c.idsOK

open Faithful Faithful.Model in
/-- The conditions of `others` but the two of `faithCoreOK` that compare names (`namesApartK`,
`itesApart`), each decided on its own. -/
def light (c : Semantics) : Bool :=
  c.sortedOK && c.predsApart && c.idsOK && namesNumbered c && genWf c && collSortsOK c &&
    collsOK c && patHeadsOK c && LitsApart c && sortsNumbered c && kindsApart c && ctorsOnce c && fnsApart c

open Faithful Faithful.Model in
theorem others_of {c : Semantics} (h : light c = true) (hn : namesApartFast c = true) (hi : itesApart c = true) :
    others c = true := by
  unfold light at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  unfold others Semantics.faithCoreOK
  simp only [h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, namesApartK_of_fast hn, hi, Bool.and_self]

theorem coreOK_of {c : Semantics} (h : others c = true) (ho : c.overloadsOK = true) : c.coreOK = true := by
  show (others c && c.overloadsOK) = true
  rw [h, ho]; rfl

/-! ## The signature and the clauses -/

def expS : Srt := nRegSorts
def kl : Sym := nRegSyms + 3
def eS : Sym := nRegSyms + 5
def negInt : Sym := nRegSyms + 6
def negExp : Sym := nRegSyms + 7

/-- `negInt(I) = 0 -Int I`. -/
def negIntCl : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs := .app intSub [intT 0, .var 0], ens := none }
def negIntFn : Fn := ⟨negInt, [Srt.int], Srt.int, [negIntCl], true⟩

/-- The symbol-overload sentence as a clause of `negExp`: `aside`, priority 0. -/
def ovlCl : Clause :=
  { vars := [Srt.int], pats := [.inj Srt.int expS (.var 0)], req := none,
    rhs := .inj Srt.int expS (.app negInt [.var 0]), ens := none, prio := 0, aside := true }

/-- `negExp(e #as G0) = G0`. -/
def userCl : Clause := { vars := [expS], pats := [.as (.app eS []) 0], req := none, rhs := .var 0, ens := none }

/-- A clause of priority 0, not `aside`, applying at every argument: `negExp(X) => e`. -/
def cl0 : Clause := { vars := [expS], pats := [.var 0], req := none, rhs := .app eS [], ens := none, prio := 0 }

/-- `negExp(_) => e [owise]`: its premise negates the user clause only (e5-ovl-fn-fn-owise). -/
def owiseCl : Clause := { vars := [expS], pats := [.var 0], req := none, rhs := .app eS [], ens := none, prio := 200 }

def negFn (cls : List Clause) : Fn := ⟨negExp, [expS], expS, cls, false⟩

def sem (cls : List Clause) : Semantics :=
  { lib := lib0
    sortNames := ["Exp", "KCell", "KCellOpt"]
    symNames := ["LblisExp", "LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lble",
      "LblnegInt", "LblnegExp"]
    userSorts := [Srt.top, Srt.topFrag, expS, expS + 1, expS + 2, Srt.counter, Srt.counterOpt]
    ctors := cellCtors (expS + 1) kl ++ [⟨eS, [], expS⟩]
    fns := [negIntFn, negFn cls]
    userSubsorts := (Srt.int, expS) :: cellSubsorts (expS + 1)
    pgmSort := Srt.k
    rules := [] }

/-- e5-ovl-fn-fn. -/
def c : Semantics := sem [ovlCl, userCl]
/-- A competitor of priority 0 beside the `aside` clause. -/
def cC : Semantics := sem [ovlCl, userCl, cl0]
/-- e5-ovl-fn-fn-owise. -/
def cO : Semantics := sem [ovlCl, userCl, owiseCl]

/-! ## Values and evaluation facts shared by the three semantics -/

def v3 : GroundTerm := .dv Srt.int (.int 3)
def vm3 : GroundTerm := .dv Srt.int (.int (-3))
/-- `inj{Int,Exp}(3)` -/
def i3 : GroundTerm := .inj Srt.int expS v3
/-- `inj{Int,Exp}(-3)` -/
def im3 : GroundTerm := .inj Srt.int expS vm3
/-- `e` -/
def ve : GroundTerm := .ctor eS []

theorem i3_ne_ve : i3 ≠ ve := by simp [i3, ve]
theorem im3_ne_ve : im3 ≠ ve := by simp [im3, ve]

section Shared

variable (cls : List Clause)

/-- The two functions, found by `lookupFn` (decided for each semantics below: `lookupFn` does not
reduce over an unknown list of clauses). -/
def Lookups : Prop := (sem cls).lookupFn negInt = some negIntFn ∧ (sem cls).lookupFn negExp = some (negFn cls)

theorem ws1 {s : Srt} {v : GroundTerm} (hv : (sem cls).sortOf v = some s) :
    (sem cls).WellSorted [s] [(0, v)] := fun i s' h => by
  cases i with
  | zero => cases h; exact ⟨v, rfl, hv⟩
  | succ i => simp at h

theorem sort_v3 : (sem cls).sortOf v3 = some Srt.int := rfl
theorem sort_ve : (sem cls).sortOf ve = some expS := rfl

theorem isCtor_e : (sem cls).isCtor eS = true := rfl
theorem isCtor_negInt : (sem cls).isCtor negInt = false := rfl
theorem isCtor_intSub : (sem cls).isCtor intSub = false := rfl
theorem isParam_negInt : (sem cls).isParam negInt = false := rfl
theorem hookRes_sub : (sem cls).hookRes intSub [.dv Srt.int (.int 0), v3] = some (some vm3) := rfl

/-- `negInt(3)` is `-3`, by its clause. -/
theorem eval_negInt3 (hl : Lookups cls) : Eval (sem cls) negInt [v3] (some vm3) :=
  .clause (cl := negIntCl) (σ := [(0, v3)]) hl.1 (by simp [negIntFn])
    (ws1 cls (sort_v3 cls)) (.cons (.var rfl) .nil) (fun t ht => by cases ht) .top
    (fun cl' h _ hlt => by
      simp only [negIntFn, List.mem_singleton] at h
      subst h; exact absurd hlt (Nat.lt_irrefl _))
    rfl (.hook (isCtor_intSub cls) rfl (.cons .dv (.cons .var .nil))
      (fun vs hvs => by
        injection hvs with hvs
        subst hvs
        exact hookRes_sub cls)
      (fun h => by cases h))
    (fun t ht => by cases ht) .top

/-- The `aside` clause's right side at `K0 := 3` is `inj -3`. -/
theorem rhs_ovl3 (hl : Lookups cls) : EvalTerm (sem cls) [(0, v3)] ovlCl.rhs (some im3) := by
  have h : EvalTerm (sem cls) [(0, v3)] (.inj Srt.int expS (.app negInt [.var 0]))
      ((some vm3).map (injNormal Srt.int expS)) :=
    .inj (.call (isCtor_negInt cls) rfl (.cons .var .nil) rfl (eval_negInt3 cls hl) (isParam_negInt cls))
  exact h

theorem match_ovl3 : PatVals (sem cls) [(0, v3)] ovlCl.pats [i3] := by
  have h : PatVal (sem cls) [(0, v3)] (.inj Srt.int expS (.var 0)) (injNormal Srt.int expS v3) := .inj (.var rfl)
  exact .cons h .nil

/-- **At `inj 3`, `inj -3`, by the `aside` clause** of priority 0: no clause is below it. -/
theorem eval_ovl3 (hl : Lookups cls) (hmem : ovlCl ∈ cls) : Eval (sem cls) negExp [i3] (some im3) :=
  .clause (cl := ovlCl) (σ := [(0, v3)]) hl.2 hmem (ws1 cls (sort_v3 cls))
    (match_ovl3 cls) (fun t ht => by cases ht) .top (fun _ _ _ hlt => absurd hlt (Nat.not_lt_zero _))
    rfl (rhs_ovl3 cls hl) (fun t ht => by cases ht) .top

/-- The pattern of `e` denotes `e` only. -/
theorem patVal_e {σ : Subst} {v : GroundTerm} (h : PatVal (sem cls) σ (.app eS []) v) : v = ve := by
  cases h with
  | ctor _ hs => cases hs; rfl
  | hook hp _ _ => cases hp
  | coll hc _ _ _ => cases hc
  | ovl hc _ _ _ => cases hc

/-- The user clause fails at `inj 3`: its pattern `e #as G0` does not denote it. -/
theorem userCl_fails_i3 : Fails (sem cls) [i3] userCl := .intro fun σ _ hp => by
  cases hp with
  | cons h _ =>
    cases h with
    | as h' _ => exact absurd (patVal_e cls h') i3_ne_ve

end Shared

/-! ## e5-ovl-fn-fn -/

open Faithful.Model in
theorem light_c : light c = true := by decide +kernel

open Faithful.Model in
theorem names_c : namesApartFast c = true := by decide +kernel

open Faithful.Model in
theorem ites_c : itesApart c = true := by decide_cheap

theorem ovls_c : c.overloadsOK = true := by decide +kernel

/-- **`coreOK`**, with the `aside` clause of priority 0 among `negExp`'s clauses. -/
theorem coreOK_c : c.coreOK = true := coreOK_of (others_of light_c names_c ites_c) ovls_c

theorem lookups_c : Lookups [ovlCl, userCl] := ⟨rfl, rfl⟩
theorem lookups_cC : Lookups [ovlCl, userCl, cl0] := ⟨rfl, rfl⟩
theorem lookups_cO : Lookups [ovlCl, userCl, owiseCl] := ⟨rfl, rfl⟩

/-- **`negExp(inj 3)` evaluates to `inj -3`**, by the `aside` clause. -/
theorem eval_inj3 : Eval c negExp [i3] (some im3) := eval_ovl3 _ lookups_c (by simp)

/-- **`negExp(e)` evaluates to `e`**, by the user clause: the only clause below it is `aside`. -/
theorem eval_e : Eval c negExp [ve] (some ve) :=
  .clause (cl := userCl) (σ := [(0, ve)]) lookups_c.2 (by simp [negFn]) (ws1 _ (sort_ve _))
    (.cons (.as (.ctor (isCtor_e _) .nil) rfl) .nil) (fun t ht => by cases ht) .top
    (fun cl' h ha hlt => by
      simp only [negFn, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · cases ha
      · exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => by cases ht) .top

open Det in
theorem obligations_c : c.rankObligations [negInt, negExp] ++ c.decObligationsL = [] ∧
    c.totalObligationsRP [negInt, negExp] [] = [] ∧ c.agreeObligationsI = [] ∧
    c.matchObligationsL = ([] : List (Nat × Nat)) ∧ c.readsConfined = false := by decide +kernel

theorem sortedOK_c : c.sortedOK = true := by decide_cheap

/-- **`FnHyp`**: every obligation the deciders leave is empty (the two clauses of `negExp` meet at no
argument), and `OpenDecided`, `OpenLaws` from a definition that reads no confined sort and is
well sorted. -/
theorem fnHyp_c : FnHyp c := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := obligations_c
  exact fnHyp_of_fnObligations (ord := [negInt, negExp]) (tp := []) coreOK_c
    (Semantics.rightHeld_of_valued (by decide +kernel)) ParamsTotal.nil
    ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
     fun f hf => by rw [h2] at hf; exact absurd hf List.not_mem_nil,
     fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
     fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil,
     openDecided_of_readsConfined h5, openLaws_of_plain (by decide +kernel)⟩

/-- **`ClausesAgree`** of `negExp`: the `aside` clause and the user clause compete (the `aside` one is
of the smaller priority) and meet at no argument. -/
theorem agree_c : ClausesAgree c (negFn [ovlCl, userCl]) := fnHyp_c.2.2.1 _ (by simp [c, sem])

/-! ## A competitor of priority 0 beside the `aside` clause -/

theorem appliesC_ovl : ovlCl.AppliesAt cC [(0, v3)] [i3] :=
  ⟨(ws1 _ (sort_v3 _)).at _, match_ovl3 _, (fun t ht => by cases ht), .top⟩

theorem appliesC_cl0 : cl0.AppliesAt cC [(0, i3)] [i3] :=
  ⟨(ws1 _ (by decide +kernel)).at _, .cons (.var rfl) .nil, (fun t ht => by cases ht), .top⟩

theorem pairC : (ovlCl, cl0) ∈ pairs (negFn [ovlCl, userCl, cl0]).clauses := by simp [negFn, pairs]

open Faithful.Model in
theorem light_cC : light cC = true := by decide +kernel
open Faithful.Model in
theorem names_cC : namesApartFast cC = true := by decide +kernel
open Faithful.Model in
theorem ites_cC : itesApart cC = true := by decide_cheap
theorem ovls_cC : cC.overloadsOK = true := by decide +kernel

/-- `coreOK` admits the competitor beside the `aside` clause. -/
theorem coreOK_cC : cC.coreOK = true := coreOK_of (others_of light_cC names_cC ites_cC) ovls_cC

/-- **The pair competes, and `ClausesAgree` reads it**: both are of priority 0, and both apply at
`inj 3`. -/
theorem compete_reads : ovlCl.prio = cl0.prio ∧
    (ClausesAgree cC (negFn [ovlCl, userCl, cl0]) → Coherent cC ovlCl cl0 ∧ Coherent cC cl0 ovlCl) :=
  ⟨rfl, fun h => h ovlCl cl0 pairC (.inl rfl)⟩

/-- `negExp(inj 3)` is `e` by the competitor (nothing is below priority 0). -/
theorem evalC_cl0 : Eval cC negExp [i3] (some ve) :=
  .clause (cl := cl0) (σ := [(0, i3)]) lookups_cC.2 (by simp [negFn])
    ((wellSortedAt_univ rfl).mp appliesC_cl0.1)
    appliesC_cl0.2.1 (fun t ht => by cases ht) .top (fun _ _ _ hlt => absurd hlt (Nat.not_lt_zero _))
    rfl (.ctor (isCtor_e _) .nil) (fun t ht => by cases ht) .top

/-- Two results at `inj 3`: not `FnDet`. -/
theorem not_fnDet_C : ¬ FnDet cC := fun h =>
  im3_ne_ve (Option.some.inj (h _ _ _ _ (eval_ovl3 _ lookups_cC (by simp)) evalC_cl0))

/-- **Not `ClausesAgree`**: the competing pair decides at `inj 3` with `e` and `inj -3`. -/
theorem not_agree_C : ¬ ClausesAgree cC (negFn [ovlCl, userCl, cl0]) := fun h => by
  have hco := ((compete_reads.2 h).2)
  have hdet : HDet cC [(0, i3)] cl0.rhs := by
    intro u hu r r' h1 h2
    simp only [cl0, subterms, subtermsList, List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu
    have key : ∀ r, EvalTerm cC [(0, i3)] (.app eS []) r → r = some ve := fun r h => by
      cases h with
      | ctor _ hts => cases hts; rfl
      | hook hc _ _ _ _ => cases hc
      | param hc _ _ _ _ => cases hc
      | call hc _ _ _ _ _ => cases hc
      | callUndef hc _ _ _ _ => cases hc
      | ovl hc _ _ => cases hc
      | ovlFn hc _ => cases hc
    rw [key r h1, key r' h2]
  have hdec0 : cl0.Decides cC (negFn [ovlCl, userCl, cl0]) [(0, i3)] [i3] :=
    ⟨appliesC_cl0, fun _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)⟩
  have hdecO : ovlCl.Decides cC (negFn [ovlCl, userCl, cl0]) [(0, v3)] [i3] :=
    ⟨appliesC_ovl, fun _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)⟩
  rcases hco [i3] [(0, i3)] [(0, v3)] appliesC_cl0 appliesC_ovl (fun t ht => by cases ht)
      (fun _ _ => hdet) (fun _ t ht => by cases ht) (fun hne => absurd rfl hne)
      ⟨negExp, _, lookups_cC.2, by simp [negFn], by simp [negFn], hdec0, hdecO⟩ with
    ⟨-, -, hrhs, -⟩ | hr
  · simp only [cl0, ovlCl] at hrhs; cases hrhs
  · exact im3_ne_ve (Option.some.inj (hr (some ve) (some im3)
      (.inl ⟨rfl, .inl ⟨(fun t ht => by cases ht), .top, EvalTerm.ctor (isCtor_e _) .nil⟩⟩)
      (.inl ⟨rfl, .inl ⟨(fun t ht => by cases ht), .top, rhs_ovl3 _ lookups_cC⟩⟩))).symm

/-! ## e5-ovl-fn-fn-owise -/

open Faithful.Model in
theorem light_cO : light cO = true := by decide +kernel
open Faithful.Model in
theorem names_cO : namesApartFast cO = true := by decide +kernel
open Faithful.Model in
theorem ites_cO : itesApart cO = true := by decide_cheap
theorem ovls_cO : cO.overloadsOK = true := by decide +kernel

/-- `coreOK` admits the `[owise]` clause beside the `aside` one. -/
theorem coreOK_cO : cO.coreOK = true := coreOK_of (others_of light_cO names_cO ites_cO) ovls_cO

/-- `negExp(inj 3)` is `inj -3` by the `aside` clause. -/
theorem eval_ovl_inj3_O : Eval cO negExp [i3] (some im3) := eval_ovl3 _ lookups_cO (by simp)

/-- `negExp(inj 3)` is `e` by the `[owise]` clause: below it, the user clause fails at `inj 3` and the
overload clause is `aside`. -/
theorem eval_owise_inj3 : Eval cO negExp [i3] (some ve) :=
  .clause (cl := owiseCl) (σ := [(0, i3)]) lookups_cO.2 (by simp [negFn]) (ws1 _ (by decide +kernel))
    (.cons (.var rfl) .nil) (fun t ht => by cases ht) .top
    (fun cl' h ha hlt => by
      simp only [negFn, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · cases ha
      · exact userCl_fails_i3 _
      · exact absurd hlt (Nat.lt_irrefl _))
    rfl (.ctor (isCtor_e _) .nil) (fun t ht => by cases ht) .top

/-- **Two results at `inj 3`, not `FnDet`.** -/
theorem not_fnDet_O : ¬ FnDet cO := fun h =>
  im3_ne_ve (Option.some.inj (h _ _ _ _ eval_ovl_inj3_O eval_owise_inj3))

/-! ## The overload clause as the text writes it

The text's symbol-overload sentence (kore.txt //@ 263) has one attribute,
`symbol-overload{}(LblnegExp{}(), LblnegInt{}())`, and no `priority{}`. Read (`Parse.overloadEqn?`),
its priority 0 is not written (`Parse.eqnPrio`'s first component is `none`, so
`ClausePres.prioAttr` is false), its clause is `aside` (`Parse.nonExec`), and its presentation holds
the second symbol (`ClausePres.overload`). `emit` writes the clause with that attribute alone
(`clauseAttrs`), the text's attributes (`ovl_text_attrs`). -/

def ovlPres : ClausePres := { Faithful.canonClausePres ovlCl with overload := some "LblnegInt" }

/-- The text's symbol-overload sentence, in a module of its own. -/
def ovlText : String :=
  "[] module M axiom{R} \\equals{SortExp{}, R}(LblnegExp{}(inj{SortInt{}, SortExp{}}(K0:SortInt{})), " ++
  "inj{SortInt{}, SortExp{}}(LblnegInt{}(K0:SortInt{}))) " ++
  "[symbol-overload{}(LblnegExp{}(), LblnegInt{}())] endmodule []"

def ovlAxiom? : Option Kore.Axiom :=
  match Kore.parseDefinition ovlText with
  | .ok d => match d.modules.head?.bind (·.sentences.head?) with
    | some (.axiom a) => some a
    | _ => none
  | .error _ => none

-- the reader's priority (written, read), `aside` and second symbol of the sentence
#guard (ovlAxiom?.bind Parse.overloadEqn?).map (fun e =>
    (Parse.eqnPrio e, Parse.nonExec e, (Parse.overloadSyms? e.attrs).map (·.2))) ==
  some ((none, 0), true, some "LblnegInt")

/-- `emit`'s attributes of the clause, whatever the presentation's other parts. -/
theorem ovl_emit_attrs (p : Presentation) :
    clauseAttrs c p (negFn [ovlCl, userCl]) ovlCl ovlPres = [overloadAttr "LblnegExp" "LblnegInt"] := by
  rfl

-- they are the text's
#guard decide (ovlAxiom?.map (·.attributes) = some [overloadAttr "LblnegExp" "LblnegInt"])

end OvlFnFn

/-! The declarations above depend on no axiom but `propext`, `Classical.choice`, `Quot.sound`. -/
/-- info: 'OvlFnFn.coreOK_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.coreOK_c
/-- info: 'OvlFnFn.eval_inj3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.eval_inj3
/-- info: 'OvlFnFn.eval_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.eval_e
/-- info: 'OvlFnFn.fnHyp_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.fnHyp_c
/-- info: 'OvlFnFn.agree_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.agree_c
/-- info: 'OvlFnFn.coreOK_cC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.coreOK_cC
/-- info: 'OvlFnFn.compete_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.compete_reads
/-- info: 'OvlFnFn.not_fnDet_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.not_fnDet_C
/-- info: 'OvlFnFn.not_agree_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.not_agree_C
/-- info: 'OvlFnFn.coreOK_cO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.coreOK_cO
/-- info: 'OvlFnFn.eval_ovl_inj3_O' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.eval_ovl_inj3_O
/-- info: 'OvlFnFn.eval_owise_inj3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.eval_owise_inj3
/-- info: 'OvlFnFn.not_fnDet_O' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.not_fnDet_O
/-- info: 'OvlFnFn.ovl_emit_attrs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OvlFnFn.ovl_emit_attrs
