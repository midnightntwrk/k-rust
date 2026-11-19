/-
  KCore. A witness that `FnSolves` cannot be dropped from `consistent_of`: a semantics with
  `coreOK`, `FnDet` and `OpenLaws`, without `FnSolves`, whose `Γ` has no model.

  One function `f : Int → Int` with two equations:
  - `f(X) => 1 requires f(X) ==Int 2 [priority(40)]`;
  - `f(X) => 2 [owise]` (priority 200).
  At an integer `w`, the first equation's `requires` calls `f` at `w`, and so does the second's
  premise, which asks the first to fail: `Eval` has no derivation of `f(w)` (`f_none`). So `FnDet`
  holds (`fnDet`), and `coreOK` holds (`coreOK`, hence `OpenLaws`, `openLaws`); `FnSolves` does not
  (`not_fnSolves`): at `0` the second equation decides (the first does not apply, its `requires`
  having no result), and its right-hand side has the value `2`, which `f` does not have.

  `Γ` has no model (`no_model`), so neither has `Γc ∪ Γstep` (`not_consistent`): where
  `f(0) ==Int 2` is `true`, the first equation makes `f(0)` the value 1, and then `f(0) ==Int 2` is
  `false`; where it is not `true`, the second makes `f(0)` the value 2, and then it is `true`.
-/
import KcoreSpec.HypWf
import KcoreSpec.ClausesAgree
import KcoreSpec.MatchComplete
import KcoreSpec.SubjectReduction
import KcoreSpec.FaithfulStage4
import KcoreSpec.FaithfulNeg
import KcoreSpec.FaithfulStep
import KcoreSpec.CoreDecide
import KcoreSpec.Sound
import KcoreSpec.Obligations
import KcoreSpec.ModelUndefRhsWitness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace FnSolvesWitness

open Faithful.UndefRhsWitness (kIds cellSorts cellCtors cellSubsorts)

/-- `f`, numbered after the four cell symbols. -/
def F : Sym := nRegSyms + 4

/-- `f(X) ==Int 2`. -/
def req1 : Term := .app intEq [.app F [.var 0], .dv Srt.int (.int 2)]

/-- `f(X) => 1 requires f(X) ==Int 2 [priority(40)]`. -/
def cl1 : Clause := ⟨[Srt.int], [.var 0], some req1, .dv Srt.int (.int 1), none, 40, false, [], .top, .top⟩

/-- `f(X) => 2 [owise]`. -/
def cl2 : Clause := ⟨[Srt.int], [.var 0], none, .dv Srt.int (.int 2), none, 200, false, [], .top, .top⟩

def fF : Fn := ⟨F, [Srt.int], Srt.int, [cl1, cl2], false⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fF]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

set_option maxHeartbeats 4000000 in
theorem coreOK : c.coreOK = true := by decide_coreOK

theorem lookupF : c.lookupFn F = some fF := rfl

theorem isCtorF : c.isCtor F = false := by decide +kernel
theorem isHookF : isHook F = false := by decide +kernel
theorem isParamF : c.isParam F = false := by decide +kernel
theorem isOvlF : c.isOvl F = false := by decide +kernel
theorem isCtorEq : c.isCtor intEq = false := by decide +kernel
theorem isParamEq : c.isParam intEq = false := by decide +kernel
theorem isOvlEq : c.isOvl intEq = false := by decide +kernel

/-- `f` has no result at an integer: each derivation of `f(w)` holds one of `f(w)` inside the first
equation's `requires`. -/
theorem f_none {w : GroundTerm} (hw : c.sortOf w = some Srt.int) {res : Option GroundTerm} :
    ¬ Eval c F [w] res := by
  intro hv
  exact Eval.rec (c := c)
    (motive_1 := fun f vs _ _ => f = F → ∀ w, vs = [w] → c.sortOf w = some Srt.int → False)
    (motive_2 := fun vs cl _ => cl = cl1 → ∀ w, vs = [w] → c.sortOf w = some Srt.int → False)
    (motive_3 := fun σ cl _ => cl = cl1 → ∀ w, σ.lookup 0 = some w → c.sortOf w = some Srt.int → False)
    (motive_4 := fun σ t _ _ => (t = req1 ∨ t = .app F [.var 0]) →
      ∀ w, σ.lookup 0 = some w → c.sortOf w = some Srt.int → False)
    (motive_5 := fun σ ts _ _ => ts = [.app F [.var 0], .dv Srt.int (.int 2)] →
      ∀ w, σ.lookup 0 = some w → c.sortOf w = some Srt.int → False)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun {_ _ _ cl _ _} hfn hmem _ hmatch _ _ _ _ _ _ _ ihreq _ ihprio _ _ _ => fun hf w hvs hw => by
      subst hf; subst hvs
      rw [lookupF] at hfn; cases hfn
      simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · cases hmatch with
        | cons h1 _ => cases h1 with | var hl => exact ihreq req1 rfl (.inl rfl) w hl hw
      · exact ihprio cl1 (by simp [fF]) rfl (by decide) rfl w rfl hw)
    (fun hfn _ ihnone => fun hf w hvs hw => by
      subst hf; subst hvs
      rw [lookupF] at hfn; cases hfn
      exact ihnone cl1 (by simp [fF]) rfl w rfl hw)
    (fun {_ _ _ cl _ _ _} hfn hmem _ hmatch _ _ _ _ _ _ _ ihreq _ ihprio _ => fun hf w hvs hw => by
      subst hf; subst hvs
      rw [lookupF] at hfn; cases hfn
      simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · cases hmatch with
        | cons h1 _ => cases h1 with | var hl => exact ihreq req1 rfl (.inl rfl) w hl hw
      · exact ihprio cl1 (by simp [fF]) rfl (by decide) rfl w rfl hw)
    (fun {_ _ _ cl _ _} hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => fun hf _ _ _ => by
      subst hf
      rw [lookupF] at hfn; cases hfn
      simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> exact absurd rfl hne)
    (fun {_ _ _ cl _} hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => fun hf _ _ _ => by
      subst hf
      rw [lookupF] at hfn; cases hfn
      simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> exact absurd rfl hne)
    (fun _ ih => fun hcl w hvs hw => by
      subst hcl; subst hvs
      refine ih [(0, w)] (fun i _ s hi => ?_) (.cons (.var rfl) .nil) rfl w rfl hw
      match i, hi with
      | 0, hi => simp only [cl1, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨w, rfl, hw⟩
      | _ + 1, hi => simp [cl1] at hi)
    (fun ht _ _ ihe => fun hcl w hl hw => by
      subst hcl
      simp only [cl1, Option.some.injEq] at ht
      subst ht
      exact ihe (.inl rfl) w hl hw)
    (fun h _ => fun hcl _ _ _ => by
      subst hcl
      exact absurd (Holds.top_eq h) (by simp))
    (fun h => by rcases h with h | h <;> cases h)
    (fun h => by rcases h with h | h <;> cases h)
    (fun _ _ => fun h => by rcases h with h | h <;> cases h)
    (fun hk _ _ => fun h => by
      rcases h with h | h <;> cases h
      · exact absurd hk (by rw [isCtorEq]; decide)
      · exact absurd hk (by rw [isCtorF]; decide))
    (fun _ hhk _ _ _ ihts => fun h w hl hw => by
      rcases h with h | h <;> cases h
      · exact ihts rfl w hl hw
      · exact absurd hhk (by rw [isHookF]; decide))
    (fun _ _ hp _ _ _ => fun h => by
      rcases h with h | h <;> cases h
      · exact absurd hp (by rw [isParamEq]; decide)
      · exact absurd hp (by rw [isParamF]; decide))
    (fun _ hh hts hvs _ _ _ ihf => fun h w hl hw => by
      rcases h with h | h <;> cases h
      · exact absurd hh (by decide)
      · cases hts with
        | cons h1 h2 =>
          cases h2; cases h1
          rw [hl] at hvs
          simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
          exact ihf rfl w hvs.symm hw)
    (fun _ hh hts hvs _ _ => fun h w hl hw => by
      rcases h with h | h <;> cases h
      · exact absurd hh (by decide)
      · cases hts with
        | cons h1 h2 =>
          cases h2; cases h1
          rw [hl] at hvs
          simp [allSome] at hvs)
    (fun _ ho _ _ _ => fun h => by
      rcases h with h | h <;> cases h
      · exact absurd ho (by rw [isOvlEq]; decide)
      · exact absurd ho (by rw [isOvlF]; decide))
    (fun _ ho _ _ _ _ _ _ _ => fun h => by
      rcases h with h | h <;> cases h
      · exact absurd ho (by rw [isOvlEq]; decide)
      · exact absurd ho (by rw [isOvlF]; decide))
    (fun h => by cases h)
    (fun _ _ ih1 _ => fun h w hl hw => by
      cases h
      exact ih1 (.inr rfl) w hl hw)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    hv rfl w rfl hw

/-- The first equation's `requires` has no result at a substitution giving `X` an integer. -/
theorem req1_none {σ : Subst} {w : GroundTerm} (hl : σ.lookup 0 = some w) (hw : c.sortOf w = some Srt.int)
    {res : Option GroundTerm} : ¬ EvalTerm c σ req1 res := by
  intro h
  cases h with
  | ctor hk _ => exact absurd hk (by rw [isCtorEq]; decide)
  | hook _ _ hts _ _ =>
    cases hts with
    | cons h1 _ =>
      cases h1 with
      | ctor hk _ => exact absurd hk (by rw [isCtorF]; decide)
      | hook _ hhk _ _ _ => exact absurd hhk (by rw [isHookF]; decide)
      | param _ _ hp _ _ => exact absurd hp (by rw [isParamF]; decide)
      | call _ _ hts' hvs hf _ =>
        cases hts' with
        | cons h1' h2' =>
          cases h2'; cases h1'
          rw [hl] at hvs
          simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
          subst hvs
          exact f_none hw hf
      | callUndef _ _ hts' hvs _ =>
        cases hts' with
        | cons h1' h2' => cases h2'; cases h1'; rw [hl] at hvs; simp [allSome] at hvs
      | ovl _ ho _ => exact absurd ho (by rw [isOvlF]; decide)
      | ovlFn _ ho => exact absurd ho (by rw [isOvlF]; decide)
  | param _ _ hp _ _ => exact absurd hp (by rw [isParamEq]; decide)
  | call _ hh _ _ _ _ => exact absurd hh (by decide)
  | callUndef _ hh _ _ _ => exact absurd hh (by decide)
  | ovl _ ho _ => exact absurd ho (by rw [isOvlEq]; decide)
  | ovlFn _ ho => exact absurd ho (by rw [isOvlEq]; decide)

/-- **`FnDet` holds**: the deciders confirm coherence, every clause fixed by its patterns and no
agreement named (`matchIndependentAll_of_sortedOK`, `clausesAgree_of_sortedOK`). -/
theorem fnDet : FnDet c := by
  have hok : c.sortedOK = true := by decide +kernel
  have hsr : c.srReady = true := by decide +kernel
  have hmr : c.matchReady = true := by decide +kernel
  have hag : c.agreeObligations = [] := by decide +kernel
  have hcf : c.clausesFixed = true := by decide +kernel
  refine fnDet_of_coherent (coherentAll_of_parts
    (matchIndependentAll_of_sortedOK hok (Semantics.fnsNoExs_of_all (by decide +kernel)) hmr (.of_fixed hcf (Exec.matchCtx_of hmr).noOvl)) fun f fn hfn => ?_)
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with h | h
  · exact clausesAgree_of_sortedOK hok (Semantics.fnsNoExs_of_all (by decide +kernel)) hsr hmr (fun f hf => by rw [hag] at hf; nomatch hf) fn h
  · exact sortPreds_agree h

def i0 : GroundTerm := .dv Srt.int (.int 0)

theorem i0_int : c.sortOf i0 = some Srt.int := by decide +kernel

/-- **`FnSolves` fails**: at `0` the `[owise]` equation decides, its right-hand side has the value
`2`, and `f` has no value there. -/
theorem not_fnSolves : ¬ FnSolves c := by
  intro hs
  let σ : Subst := [(0, i0)]
  have hσ : c.WellSorted cl2.vars σ := fun i s hi => by
    match i, hi with
    | 0, hi => simp only [cl2, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨i0, rfl, i0_int⟩
    | _ + 1, hi => simp [cl2] at hi
  have hdec : cl2.DecidesAt c fF σ [i0] := by
    refine ⟨⟨hσ.at _, .cons (.var rfl) .nil, (fun _ ht => by cases ht), .top⟩, fun cl' hcl' _ hlt σ' _ hm hq => ?_⟩
    simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl
    · cases hm with
      | cons h1 _ => cases h1 with | var hl => exact req1_none hl i0_int (hq.1 req1 rfl)
    · exact absurd hlt (Nat.lt_irrefl _)
  have hE := (hs fF (by simp [c]) [i0] (by decide +kernel) cl2 (by simp [fF]) σ hdec (.dv Srt.int (.int 2))).mpr
    ⟨σ, AgreeOff.refl _ _, hσ, .dv, fun t ht => by simp [cl2] at ht, .top⟩
  exact f_none i0_int hE

/-! ## No model of `Γ`

In a model, write `S` for the denotation of `f(0)` and `Q` for that of `f(0) ==Int 2` (`F0P`,
`QP`). The first equation's premise at `X := 0` is `⌈Q = true⌉`, read over the elements of Bool;
the second's is that premise's negation (its exclusion). If `Q` is `true` on Bool, the first
equation makes `S` the value 1, so `Q` is the value of `1 ==Int 2`, `false`; if not, the second
makes `S` the value 2, so `Q` is the value of `2 ==Int 2`, `true`. Either way two distinct Bool
values would have one element. -/

section NoModel

open ML Faithful
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- A clause's premise holds where its patterns match and its `requires` is `true` on the elements
of Bool (`premise_holds4`, with its `requires` read on Bool only, as the premise reads it). -/
theorem premise_holdsB {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c)
    (hph : patHooksApart c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {fn : Fn} (hfnm : fn ∈ c.allFns) {cl : Clause} {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hpats : sortsOfTerms c.patCtxNF cl.vars cl.pats = some fn.args)
    {σB : M} (hσB1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Bool")) a ↔ a = σB) (hσB2 : IsSort I σB)
    {tbl : VarTable} {e : Valuation M} {σr m0 : M} (hag : Agrees c I tbl (canonVars c cl.vars) σ' e)
    (hX : ∀ (j : Nat) w s, ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = elemOf c I w)
    (hRv : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) (hσr2 : IsSort I σr) (hm0 : Inh I σr m0)
    (ihreq : ∀ t, cl.req = some t → ∀ a, Inh I σB a →
      ((KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e a ↔
        (den c (bool true)).interpret I e a)) :
    (KoreAML.tr ⟨tbl, []⟩ (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
      (Term.koreList c (canonVars c cl.vars) cl.pats))).interpret I e m0 := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hnum := hnn.2.2 fn hfnm
  unfold premise
  rw [tr_and2, KoreAML.interp_sAnd]
  refine ⟨?_, argsConj_den4 hI hnn.1 hph htr hσ' (canonVars_length c cl.vars) hag hRv hσr2 hm0 hmatch fn.args 0
    hpats (fun s hs => hnum s (List.mem_cons_of_mem _ hs)) ?_⟩
  · cases hq : cl.req with
    | none =>
      simp only [Option.map_none, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sTop hD isFree_R, KoreAML.interp_inhOf_of hRv]
      exact hm0
    | some t =>
      simp only [Option.map_some, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hRv hσB2 hσr2]
      refine ⟨hm0, fun a ha => ?_⟩
      rw [ihreq t hq a ha, KoreAML.tr_dv]
      unfold den KoreAML.den bool
      rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
      exact Iff.rfl
  · intro k s w hk hw m'
    rw [Nat.zero_add]
    obtain ⟨w', hw', hsw⟩ := sortsOf_get hws hk
    rw [hw] at hw'; cases hw'
    rw [hX k w (c.sortName s) hw (by rw [List.getElem?_map, hk]; rfl)]
    exact ((elemOf_spec hI hsw e).1 m').symm

/-- A competing clause's exclusion is empty at the arguments `ws`, at a valuation that gives each
formal argument the element of the argument and the sort variable `R` a sort. -/
def ExclEmptyAt (c : Semantics) (I : Interpretation KoreAML.Sym M) (fn : Fn) (cl : Clause)
    (ws : List GroundTerm) : Prop :=
  ∀ {tbl : VarTable}, (∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) →
    (∀ (j : Nat) s, fn.args[j]? = some s → VarKey.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)) ∈ tbl) →
    VarKey.sortVar "R" ∈ tbl →
    ∀ {e : Valuation M}, (∀ (j : Nat) w s, ws[j]? = some w → fn.args[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) = elemOf c I w) →
    ∀ {σR : M}, e.evalEvar (tbl.ev (.sortVar "R")) = σR → IsSort I σR →
    ∀ m, ¬ (KoreAML.tr ⟨tbl, []⟩ (exclusion c fn cl (canonClausePres cl))).interpret I e m

/-- A clause whose patterns are plain has an empty exclusion at `ws` where, at every match, its
`requires` is not `true` on the elements of Bool (`exclusion_empty`, with that reading of failing). -/
theorem exclEmptyAt_of {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c) (hg : genWf c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts) (hnm : NamesPlain c)
    {fn : Fn} {cl : Clause} (hpre : cl.pre = .top)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats) (hplain : plainPats c cl.pats = true)
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σB : M} (hσB1 : ∀ a, I.evalSymb (.sort ("Sort" ++ "Bool")) a ↔ a = σB) (hσB2 : IsSort I σB)
    (hnot : ∀ σ, c.WellSorted cl.vars σ → PatVals c σ cl.pats ws → ∀ (tbl : VarTable) (e : Valuation M),
      Agrees c I tbl (canonVars c cl.vars) σ e → ∃ t, cl.req = some t ∧
        ¬ ∀ a, Inh I σB a → ((KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e a ↔
          (den c (bool true)).interpret I e a)) :
    ExclEmptyAt c I fn cl ws := by
  intro tbl hkeys hXkeys hRkey e hX σR hR hσR m hm
  rw [exclusion_top _ hpre (binds_of_forall hbinds)] at hm
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  let vs := canonVars c cl.vars
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  have hm' : (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll KoreAML.R (vs.map KoreAML.Var.kore)
      (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c vs)) (Term.koreList c vs cl.pats)))).interpret I e m := hm
  obtain ⟨e', hag, hguard, hbody⟩ := existsAll_elim hD _ e m hnd hsrt hm'
  have hnotb : ∀ k, k ∈ tbl → (∀ i < cl.vars.length, k ≠ canonKey c cl.vars i) →
      ∀ b ∈ vs.map KoreAML.Var.kore, tbl.ev k ≠ tbl.ev (KoreAML.evarKey b) := by
    intro k hk hne b hb heq
    obtain ⟨i, hi, rfl⟩ := canonVars_kore_mem hb
    exact hne i hi (ev_inj hk (hkeys i hi) heq)
  have he'X : ∀ (j : Nat) s, fn.args[j]? = some s →
      e'.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) =
        e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) :=
    fun j s hj => hag _ (hnotb _ (hXkeys j s hj) (fun i hi => canonKey_ne_X hI hg htr hi _ _))
  have he'R : e'.evalEvar (tbl.ev (.sortVar "R")) = e.evalEvar (tbl.ev (.sortVar "R")) :=
    hag _ (hnotb _ hRkey (fun i hi h => by rw [canonKey_eq c hi] at h; cases h))
  unfold premise at hbody
  rw [tr_and2, KoreAML.interp_sAnd] at hbody
  obtain ⟨hreq, hargs⟩ := hbody
  have hcon := argsConj_back 0 _ hargs
  have hin : ∀ i < cl.vars.length, InS I (c.sortName (cl.vars.getD i 0)) (e'.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    have hlt : i < vs.length := by rw [canonVars_length]; exact hi
    have hb : (vs.getD i default).kore ∈ vs.map KoreAML.Var.kore := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact List.mem_map_of_mem (List.getElem_mem hlt)
    exact hguard _ hb _ (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl)
  have hlenp : (Term.koreList c vs cl.pats).length = fn.args.length := by
    rw [koreList_length]; exact sortsOfTerms_length hpats
  have hall : All2 (fun φ b => φ.interpret I e' b) ((Term.koreList c vs cl.pats).map (KoreAML.tr ⟨tbl, []⟩))
      (ws.map (elemOf c I)) := by
    refine All2.of_get (by simp [hlenp, sortsOf_length hws]) (fun j φ b hφ hb => ?_)
    rw [List.getElem?_map] at hφ hb
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hφ
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hb
    have hjl : j < fn.args.length := by
      rw [← sortsOf_length hws]; exact (List.getElem?_eq_some_iff.mp hw).1
    have hs : fn.args[j]? = some fn.args[j] := List.getElem?_eq_getElem hjl
    have hl : ((fn.args.map c.sortName).zip (Term.koreList c vs cl.pats))[j]? = some (c.sortName fn.args[j], p) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨by rw [List.getElem?_map, hs]; rfl, hp⟩
    have := hcon j _ p hl
    rw [Nat.zero_add, he'X j _ hs, hX j w _ hw hs] at this
    exact this
  obtain ⟨hpv, hwit⟩ := patVals_back hI hg htr hnm (canonVars_length c cl.vars) hin hplain hpats hws hall
  obtain ⟨hws', hagr⟩ := substOf_ok hI hg htr (canonVars_length c cl.vars) (fun i hi => hwit i (hbinds i hi))
  obtain ⟨t, ht, hn⟩ := hnot _ hws' hpv tbl e' hagr
  rw [ht] at hreq
  simp only [Option.map_some, reqPat] at hreq
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1)
    (fun a => by rw [trSort_R, KoreAML.interp_evar, he'R, hR]) hσB2 hσR] at hreq
  refine hn fun a ha => (hreq.2 a ha).trans ?_
  rw [KoreAML.tr_dv]
  unfold den KoreAML.den bool
  rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
  exact Iff.rfl

/-- **A clause's equation under negated competitors, read in a model**, each competitor's exclusion
empty at the arguments (`compete_eq4`, with `ExclEmptyAt` in place of `ExclEmpty` and
`ModelFails`). -/
theorem compete_eqAt {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c)
    (hph : patHooksApart c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {others : List Clause} {cl : Clause}
    (hmem : competingEquation c fn others cl ∈ fnEquationsK c fn) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    (hpres : ∀ cl' ∈ others, cl'.pre = .top) {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hothers : ∀ cl' ∈ others, sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ i < cl'.vars.length, i ∈ varOccsList cl'.pats) ∧ (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyAt c I fn cl' ws)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hpatsN : sortsOfTerms c.patCtxNF cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {r : Option GroundTerm} (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihreq : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e r m)
    (e0 : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔ Res c I e0 r m := by
  have hpats := sortsOfTerms_all_of_nf hpatsN
  rw [competingEquation_top hpre hexs] at hmem
  have hfnm := (lookupFn_spec hfn).1
  have hD := defOK hI
  have hv := premise_vars (c := c) hpats hbinds hreqv
  let comps := others.map fun cl' => exclusion c fn cl' (canonClausePres cl')
  let P := premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
    (Term.koreList c (canonVars c cl.vars) cl.pats)
  have hP : ∀ k, k ∈ KoreAML.varsOf P →
      k ∈ KoreAML.varsOf (competingPremise (fn.args.map c.sortName) comps (cl.req.map (Term.kore c (canonVars c cl.vars)))
        (Term.koreList c (canonVars c cl.vars) cl.pats)) := fun k hk => by
    unfold competingPremise
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk))
  have hN : ∀ k, k ∈ KoreAML.varsOf (anyOfC KoreAML.R comps) →
      k ∈ KoreAML.varsOf (competingPremise (fn.args.map c.sortName) comps (cl.req.map (Term.kore c (canonVars c cl.vars)))
        (Term.koreList c (canonVars c cl.vars) cl.pats)) := fun k hk => by
    unfold competingPremise
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOf, anyOf_eq]
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hk))
  refine eqn_at hI hnn hfn (eqn_item_mem hfnm hmem) hws hσ' (fun j s hj => hP _ (hv.1 j s hj))
    (fun i hi => hP _ (hv.2.1 i hi)) (fun k hk => ?_) hrhsv hensv hr (fun tbl e σr m0 hkeys hag hX hRv hσr2 hm0 => ?_) ihrhs e0 m
  · unfold competingPremise at hk
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOf] at hk
    simp only [List.append_nil, List.mem_append] at hk
    rcases hk with hk | hk
    · rw [anyOf_eq] at hk
      obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
      obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hp', hb', hq', -⟩ := hothers cl' hcl'
      exact Or.inl (freeOf_exclusion (hpres cl' hcl') hp' hq' (binds_of_forall hb') hk)
    · exact hv.2.2 k hk
  · have hR' : e.evalEvar (tbl.ev (.sortVar "R")) = σr := (hRv _).mp (by rw [trSort_R, KoreAML.interp_evar])
    have hRkey : VarKey.sortVar "R" ∈ tbl := hkeys _ (by
      unfold competingPremise
      rw [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_singleton_self _))
    unfold competingPremise
    rw [tr_and2, KoreAML.interp_sAnd]
    refine ⟨?_, premise_holds4 hI hnn hph htr hfnm hws hσ' hmatch hpatsN hag hX hRv hσr2 hm0 (ihreq tbl e hag)⟩
    rw [KoreAML.tr, KoreAML.interp_sNot]
    refine ⟨?_, (KoreAML.interp_inhOf_of hRv).mpr hm0⟩
    rw [anyOf_eq]
    refine anyOfC_empty hD isFree_R comps (fun φ hφ => ?_)
    obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp hφ
    obtain ⟨-, hb', -, hpl'⟩ := hothers cl' hcl'
    exact hpl'
      (fun i hi => hkeys _ (hN _ (mem_varsOf_anyOfC hφ (varsOf_exclusion (hpres cl' hcl') (binds_of_forall hb') hi))))
      (fun j s hj => hkeys _ (hP _ (hv.1 j _ (by rw [List.getElem?_map, hj]; rfl))))
      hRkey (fun j w s hw hs => hX j w _ hw (by rw [List.getElem?_map, hs]; rfl)) hR' hσr2 m0

def one : GroundTerm := .dv Srt.int (.int 1)
def two : GroundTerm := .dv Srt.int (.int 2)

/-- `f(0)` in a model. -/
def F0P : KoreAML.P := symHead c F ⬝ den c i0

/-- `f(0) ==Int 2` in a model. -/
def QP : KoreAML.P := (symHead c intEq ⬝ F0P) ⬝ den c two

theorem F0P_closed : Closed F0P := (symHead_closed (c := c) F).app (den_closed c i0)

theorem QP_closed : Closed QP := ((symHead_closed (c := c) intEq).app F0P_closed).app (den_closed c two)

omit [Inhabited M] in
theorem F0_den (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c F (GroundTerm.koreList c [i0]))).interpret I e m ↔ F0P.interpret I e m := by
  unfold KoreAML.den
  rw [tr_symApp, GroundTerm.koreList, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
  exact Iff.rfl

omit [Inhabited M] in
/-- A literal of the term language denotes its value. -/
theorem dv_den {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} (s : Srt) (lit : Lit) (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs (.dv s lit))).interpret I e m ↔ (den c (.dv s lit)).interpret I e m := by
  rw [Term.kore]; unfold den KoreAML.den; rw [GroundTerm.kore]; unfold srtOf
  rw [KoreAML.tr_dv, KoreAML.tr_dv]

omit [Inhabited M] in
/-- The first equation's `requires`, at a valuation agreeing with a substitution that gives `X` the
value 0, denotes `Q`. -/
theorem req_den {σ : Subst} {tbl : VarTable} {e : Valuation M} (hl : σ.lookup 0 = some i0)
    (hag : Agrees c I tbl (canonVars c cl1.vars) σ e) (m : M) :
    (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl1.vars) req1)).interpret I e m ↔ QP.interpret I e m := by
  unfold req1 QP F0P
  rw [kore_app, tr_symApp, Term.koreList, Term.koreList, Term.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons,
    KoreAML.trArgs_nil]
  refine KoreAML.interp_app_congr (KoreAML.interp_app_congr (fun _ => Iff.rfl) (fun m => ?_)) (fun m => dv_den _ _ m) m
  rw [kore_app, tr_symApp, Term.koreList, Term.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
  refine KoreAML.interp_app_congr (fun _ => Iff.rfl) (fun m => ?_) m
  rw [tr_var]
  exact hag 0 i0 (by rw [canonVars_length]; decide) hl m

omit [Inhabited M] in
/-- Where `f(0)` denotes a value v, `Q` denotes `v ==Int 2`. -/
theorem QP_of {e : Valuation M} {v : GroundTerm} (hS : ∀ m, F0P.interpret I e m ↔ (den c v).interpret I e m) (m : M) :
    QP.interpret I e m ↔ (KoreAML.den (symApp c intEq (GroundTerm.koreList c [v, two]))).interpret I e m := by
  unfold QP KoreAML.den
  rw [tr_symApp, GroundTerm.koreList, GroundTerm.koreList, GroundTerm.koreList, KoreAML.trArgs_cons,
    KoreAML.trArgs_cons, KoreAML.trArgs_nil]
  exact KoreAML.interp_app_congr (KoreAML.interp_app_congr (fun _ => Iff.rfl) hS) (fun _ => Iff.rfl) m

theorem intEq_sig : (⟨intEq, [Srt.int, Srt.int], Srt.bool⟩ : CtorSig) ∈ hookSigs := by decide

/-- `v ==Int 2` in a model is the hook's value. -/
theorem intEq_den (hI : I ⊧ᴵP Γ c) {v : GroundTerm} (hvs : c.sortsOf [v, two] = some [Srt.int, Srt.int]) {b : Bool}
    (hr : c.hookRes intEq [v, two] = some (some (bool b))) (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c intEq (GroundTerm.koreList c [v, two]))).interpret I e m ↔ (den c (bool b)).interpret I e m :=
  (KoreAML.interp_equal (defOK hI)).mp (sat_hookRes hI intEq_sig hvs hr e default) m

theorem one_sort : c.sortOf one = some Srt.int := by decide +kernel
theorem two_sort : c.sortOf two = some Srt.int := by decide +kernel

/-- **`Γ` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  obtain ⟨hok, hsr, hnn, hg, hph, -, -, -, hno⟩ := hypSound_of_core coreOK
  haveI : OvlOK c := hno
  have htr := (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)).trans
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hfnm : fF ∈ c.allFns := List.mem_append_left _ (List.mem_singleton_self _)
  have hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true := by
    decide +kernel
  obtain ⟨hpats1, hbinds1, -⟩ := clause_ctx hok hbc hfnm (cl := cl1) (List.mem_cons_self ..)
  obtain ⟨hpats2, hbinds2, -⟩ := clause_ctx hok hbc hfnm (cl := cl2) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hws : c.sortsOf [i0] = some fF.args := by decide +kernel
  have hpats1N := Semantics.pats_nf (OvlOK.hyp inferInstance htr) hfnm (cl := cl1) (List.mem_cons_self ..) hpats1
  have hpats2N := Semantics.pats_nf (OvlOK.hyp inferInstance htr) hfnm (cl := cl2) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hpats2
  have hreqv1 : ∀ t, cl1.req = some t → ∀ i ∈ varOccs t, i < cl1.vars.length := fun t ht => by
    cases ht; decide
  let σ1 : Subst := [(0, i0)]
  have hσ1 : ∀ cl : Clause, cl.vars = [Srt.int] → c.WellSorted cl.vars σ1 := fun cl hv i s hi => by
    rw [hv] at hi
    match i, hi with
    | 0, hi => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨i0, rfl, i0_int⟩
    | _ + 1, hi => simp at hi
  let e0 : Valuation M := KoreAML.val0
  have hinT : Inh I σB (elemOf c I (bool true)) := by
    have := (elemOf_spec hI (sortOf_bool (c := c) true) e0).2
    rw [sortName_bool] at this
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσB1).mp this
  by_cases hP : ∀ a, Inh I σB a → (QP.interpret I e0 a ↔ (den c (bool true)).interpret I e0 a)
  · -- the first equation: `f(0)` is 1, so `Q` is `false`
    have hmem : clauseEquation c fF cl1 ∈ fnEquationsK c fF := by
      have h : prioEquation c fF cl1 = clauseEquation c fF cl1 := by
        unfold prioEquation; rw [show lowerClauses fF cl1 = [] from rfl]; rfl
      rw [fnEquationsK, show fF.clauses = [cl1, cl2] from rfl, List.map_cons, h]
      exact List.mem_cons_self ..
    have hv := premise_vars (c := c) hpats1 hbinds1 hreqv1
    rw [clauseEquation_top (cl := cl1) rfl rfl] at hmem
    have h1 := fun e m => eqn_at hI hnn lookupF (prem := clausePrem c fF cl1) (eqn_item_mem hfnm hmem) hws
      (hσ1 cl1 rfl) hv.1 hv.2.1 hv.2.2 (fun _ h => by simp [cl1, varOccs] at h) (fun _ h => by simp [cl1] at h)
      (r := some one)
      (fun v hv => by cases hv; exact one_sort)
      (fun tbl e σr m0 _ hag hX hRv hσr2 hm0 =>
        premise_holdsB hI hnn hph htr hfnm hws (hσ1 cl1 rfl) (.cons (.var rfl) .nil) hpats1N hσB1 hσB2 hag hX hRv
          hσr2 hm0 (fun t ht a ha => by
            cases ht
            rw [req_den rfl hag, QP_closed.interp e e0, hP a ha]
            exact (den_closed c _).interp e0 e a))
      (fun tbl e _ => right_iff hI hnn hfnm (fun v hv => by cases hv; exact one_sort) (fun m => dv_den _ _ m)
        (fun t ht => by simp [cl1] at ht)) e m
    have hq : ∀ m, QP.interpret I e0 m ↔ (den c (bool false)).interpret I e0 m := fun m =>
      (QP_of (fun m => (F0_den e0 m).symm.trans (h1 e0 m)) m).trans
        (intEq_den hI (by decide +kernel) (by decide +kernel) e0 m)
    have hT : (den c (bool true)).interpret I e0 (elemOf c I (bool true)) :=
      ((elemOf_spec hI (sortOf_bool (c := c) true) e0).1 _).mpr rfl
    have heq := ((elemOf_spec hI (sortOf_bool (c := c) false) e0).1 _).mp ((hq _).mp ((hP _ hinT).mpr hT))
    exact absurd (values_apart hI hg htr (by decide +kernel) (sortOf_bool (c := c) true) (sortOf_bool (c := c) false)
      heq) (by decide)
  · -- the second equation: `f(0)` is 2, so `Q` is `true`
    have hmem : competingEquation c fF [cl1] cl2 ∈ fnEquationsK c fF := by
      have h : prioEquation c fF cl2 = competingEquation c fF [cl1] cl2 := by
        unfold prioEquation; rw [show lowerClauses fF cl2 = [cl1] from rfl]; rfl
      rw [fnEquationsK, show fF.clauses = [cl1, cl2] from rfl, List.map_cons, List.map_cons, h]
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have hex : ExclEmptyAt c I fF cl1 [i0] :=
      exclEmptyAt_of hI hg htr hnn.1 rfl hpats1 hbinds1 (by decide +kernel) hws hσB1 hσB2
        (fun σ _ hpv tbl e hag => ⟨req1, rfl, fun hall => hP fun a ha => by
          have hl : σ.lookup 0 = some i0 := by
            cases hpv with | cons h1 _ => cases h1 with | var hl => exact hl
          rw [QP_closed.interp e0 e, ← req_den hl hag, hall a ha]
          exact (den_closed c _).interp e e0 a⟩)
    have h2 := fun e m => compete_eqAt hI hnn hph htr lookupF (others := [cl1]) (cl := cl2) hmem rfl rfl
      (fun cl' h => by rw [List.mem_singleton] at h; subst h; rfl) hws
      (fun cl' h => by rw [List.mem_singleton] at h; subst h; exact ⟨hpats1, hbinds1, hreqv1, hex⟩)
      (hσ1 cl2 rfl) (.cons (.var rfl) .nil) hpats2N hbinds2 (fun _ h => by cases h)
      (fun _ h => by simp [cl2, varOccs] at h) (fun _ h => by simp [cl2] at h) (r := some two)
      (fun v hv => by cases hv; exact two_sort)
      (fun _ _ _ _ h => by cases h)
      (fun tbl e _ => right_iff hI hnn hfnm (fun v hv => by cases hv; exact two_sort) (fun m => dv_den _ _ m)
        (fun t ht => by simp [cl2] at ht)) e m
    exact hP fun a _ =>
      (QP_of (fun m => (F0_den e0 m).symm.trans (h2 e0 m)) a).trans
        (intEq_den hI (by decide +kernel) (by decide +kernel) e0 a)

end NoModel

/-- `OpenLaws`, the remaining hypothesis of `consistent_of`, from `coreOK`. -/
theorem openLaws : OpenLaws c := openLaws_of_plain (by decide +kernel)

/-- **Not `Consistent`**: `Γ` is part of `Γc ∪ Γstep`. -/
theorem not_consistent : ¬ Consistent c := fun ⟨M, hM, I, hI⟩ =>
  no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end FnSolvesWitness

end KCore
