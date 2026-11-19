/-
  KCore. `FnHyp` where a clause has a predicate other than `\top` in its premise (`Clause.pre`).

  `Eval`'s constructors read a clause's predicate through `Holds … cl.pre`, and `Holds` reads the
  predicate's terms through `EvalTerm`: a predicate has a truth value where each of its terms has
  a result, and a term has one where each call in it has one. So that a predicate is decided is a
  fact of the same kind as that a `requires` has a result, and it is shown the same way:

  - `Cond.evalTermsFP`: the terms a condition evaluates; `Cond.callHeadsFP`, `Fn.preHeadsFP`: the
    symbols they apply, of one condition and of the predicates of a function's clauses.
  - `holds_of_callsFP`: a well-sorted condition has a truth value at every well-sorted σ, where
    each function among the symbols its terms apply has a result at every argument list of its
    sorts. A binder's truth value is read by classical choice of its body's at each extension.
  - `eval_of_callsFP`: a function has a result at `vs` where each call in its clauses' right-hand
    sides, `requires` and `ensures` has one and each clause's predicate has a truth value at each
    match (`eval_resultRH` asks exactly this of the predicate; no reading of it as `\top`).
  - `terminates_of_calleesFP`: a function terminates where the functions its clauses apply, in a
    right-hand side, a `requires`, an `ensures` or a predicate, terminate.
  - `terminates_of_preRankFP`: every function terminates, given an order `ord` of the functions
    and the termination of those `preRankObligationsFP` names: a function not named applies, in
    its clauses' terms and predicates, only functions placed before it (`preRankedFP`), so it
    terminates by induction on its position.
  - `fnHyp_of_decidedPre`: `FnHyp` from `coreOK`, `RightHeld`, that order, and the facts the
    deciders leave. Of `FnHyp`'s six parts only termination and totality read a predicate: the
    agreement of the equations and the match independence of the clauses are decided on the
    clauses that apply (`clausesAgree_of_IO`, `matchIndependentAll_of_L`, which ask nothing of the
    predicates), and `OpenDecided` and `OpenLaws` are facts of the theory. Totality is asked
    outright: with a predicate that may be false, that the patterns and `requires` of a function's
    clauses cover its arguments does not give a clause that applies.
  - `total_of_partsFP`, `total_of_totalOKFP`: the totality check stays sound for a function whose
    own clauses have the predicate `\top`, whatever the other functions' predicates
    (`sortPreds_totalFP`: the sort predicates).

  The order here admits no call of a function to itself or to one placed after it: such a function
  is named. The rank argument for those (CallGroups.lean, DecreasingL.lean) reads `EvalCtxN`,
  whose field `pres` asks `\top` of every clause of the definition.
-/
import KcoreSpec.FnObligations
import KcoreSpec.ClausePreFn
import KcoreSpec.StepCompleteAt

set_option autoImplicit false

namespace KCore

open Det Faithful

/-- The terms a condition evaluates: the terms of its atoms, the matched term of an `exMatch`
(not its pattern, which is matched), and those of the conditions under it. -/
def Cond.evalTermsFP : Cond → List Term
  | .top | .bot => []
  | .not p => p.evalTermsFP
  | .and p q | .or p q | .implies p q => p.evalTermsFP ++ q.evalTermsFP
  | .ceil _ t => [t]
  | .equals _ t u | .mem _ t u => [t, u]
  | .exMatch _ _ _ t body => t :: body.evalTermsFP
  | .ex _ body | .all _ body => body.evalTermsFP

/-- The symbols the terms a condition evaluates apply. -/
def Cond.callHeadsFP (p : Cond) : List Sym := p.evalTermsFP.flatMap Term.heads

/-- The symbols the predicates of a function's clauses apply. `Fn.callees` holds those of the
right-hand sides, the `requires` and the `ensures`. -/
def Fn.preHeadsFP (f : Fn) : List Sym := f.clauses.flatMap fun cl => cl.pre.callHeadsFP

namespace Semantics
variable (c : Semantics)

/-- Each symbol the clauses of `fn` apply, in a right-hand side, a `requires`, an `ensures` or a
predicate, is no function of `c` or a function placed before `fn` in `ord`. -/
def preRankedFP (ord : List Sym) (fn : Fn) : Bool :=
  (fn.callees ++ fn.preHeadsFP).all fun g =>
    !(c.fns.map (·.label)).contains g || decide (ord.idxOf g < ord.idxOf fn.label)

/-- The functions `preRankedFP` does not accept: their termination is named. -/
def preRankObligationsFP (ord : List Sym) : List Sym :=
  (c.fns.filter fun f => !c.preRankedFP ord f).map (·.label)

theorem preRankObligationsFP_withHooks (H : HookParams) (ord : List Sym) :
    (c.withHooks H).preRankObligationsFP ord = c.preRankObligationsFP ord := rfl

theorem fnOvlSyms_withHooksFP (H : HookParams) : (c.withHooks H).fnOvlSyms = c.fnOvlSyms := rfl

end Semantics

variable {c : Semantics}

/-- An extension of a well-sorted σ by values of the sorts `ys` is well sorted over them. -/
theorem wellSorted_extendsFP {vars ys : List Srt} {σ σ' : Subst} (hσ : c.WellSorted vars σ)
    (he : Extends c vars.length ys σ σ') : c.WellSorted (vars ++ ys) σ' := by
  intro i s hs
  by_cases hi : i < vars.length
  · rw [List.getElem?_append_left hi] at hs
    obtain ⟨v, hv, hvs⟩ := hσ i s hs
    exact ⟨v, by rw [he.1 i hi]; exact hv, hvs⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hs
    obtain ⟨v, hv, hvs⟩ := he.2 (i - vars.length) s hs
    exact ⟨v, by rw [← hv]; congr 1; omega, hvs⟩

open Model in
open Classical in
/-- **A well-sorted condition has a truth value where the calls of its terms have results**: at
every σ that gives the variables in scope values of their sorts, where each function among the
symbols its terms apply has a result at every argument list of its sorts, and so does each
function such a symbol overloads. Nothing is asked of any other function. -/
theorem holds_of_callsFP (hsc : SortCtx c) :
    ∀ (p : Cond) {vars : List Srt} {σ : Subst}, c.condOK vars p = true → c.WellSorted vars σ →
      (∀ g ∈ p.callHeadsFP, Terminates c g ∧ OvlTerminates c g) → ∃ b, Holds c vars.length σ p b
  | .top, _, _, _, _, _ => ⟨true, .top⟩
  | .bot, _, _, _, _, _ => ⟨false, .bot⟩
  | .not p, vars, σ, hok, hσ, hc => by
    rw [Semantics.condOK] at hok
    obtain ⟨b, hb⟩ := holds_of_callsFP hsc p hok hσ hc
    exact ⟨!b, .not hb⟩
  | .and p q, vars, σ, hok, hσ, hc => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    simp only [Cond.callHeadsFP, Cond.evalTermsFP, List.flatMap_append, List.mem_append] at hc
    obtain ⟨b, hb⟩ := holds_of_callsFP hsc p hok.1 hσ (fun g hg => hc g (.inl hg))
    obtain ⟨b', hb'⟩ := holds_of_callsFP hsc q hok.2 hσ (fun g hg => hc g (.inr hg))
    exact ⟨b && b', .and hb hb'⟩
  | .or p q, vars, σ, hok, hσ, hc => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    simp only [Cond.callHeadsFP, Cond.evalTermsFP, List.flatMap_append, List.mem_append] at hc
    obtain ⟨b, hb⟩ := holds_of_callsFP hsc p hok.1 hσ (fun g hg => hc g (.inl hg))
    obtain ⟨b', hb'⟩ := holds_of_callsFP hsc q hok.2 hσ (fun g hg => hc g (.inr hg))
    exact ⟨b || b', .or hb hb'⟩
  | .implies p q, vars, σ, hok, hσ, hc => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    simp only [Cond.callHeadsFP, Cond.evalTermsFP, List.flatMap_append, List.mem_append] at hc
    obtain ⟨b, hb⟩ := holds_of_callsFP hsc p hok.1 hσ (fun g hg => hc g (.inl hg))
    obtain ⟨b', hb'⟩ := holds_of_callsFP hsc q hok.2 hσ (fun g hg => hc g (.inr hg))
    exact ⟨!b || b', .implies hb hb'⟩
  | .ceil s t, vars, σ, hok, hσ, hc => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1; rw [beq_iff_eq] at hok
    simp only [Cond.callHeadsFP, Cond.evalTermsFP, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
    obtain ⟨r, hr⟩ := evalTerm_result hsc fns_headsOK hσ t hok (fun g hg => (hc g hg).2)
      (fun g ts hts gfn hg _ vs' _ _ hsrt => (hc g (mem_heads_of_callsOf t hts)).1 gfn hg vs' hsrt)
    exact ⟨r.isSome, .ceil hr⟩
  | .equals s t u, vars, σ, hok, hσ, hc => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    simp only [Cond.callHeadsFP, Cond.evalTermsFP, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at hc
    obtain ⟨r, hr⟩ := evalTerm_result hsc fns_headsOK hσ t hok.1 (fun g hg => (hc g (.inl hg)).2)
      (fun g ts hts gfn hg _ vs' _ _ hsrt => (hc g (.inl (mem_heads_of_callsOf t hts))).1 gfn hg vs' hsrt)
    obtain ⟨r', hr'⟩ := evalTerm_result hsc fns_headsOK hσ u hok.2 (fun g hg => (hc g (.inr hg)).2)
      (fun g ts hts gfn hg _ vs' _ _ hsrt => (hc g (.inr (mem_heads_of_callsOf u hts))).1 gfn hg vs' hsrt)
    exact ⟨sameResult r r', .equals hr hr'⟩
  | .mem s t u, vars, σ, hok, hσ, hc => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    simp only [Cond.callHeadsFP, Cond.evalTermsFP, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at hc
    obtain ⟨r, hr⟩ := evalTerm_result hsc fns_headsOK hσ t hok.1 (fun g hg => (hc g (.inl hg)).2)
      (fun g ts hts gfn hg _ vs' _ _ hsrt => (hc g (.inl (mem_heads_of_callsOf t hts))).1 gfn hg vs' hsrt)
    obtain ⟨r', hr'⟩ := evalTerm_result hsc fns_headsOK hσ u hok.2 (fun g hg => (hc g (.inr hg)).2)
      (fun g ts hts gfn hg _ vs' _ _ hsrt => (hc g (.inr (mem_heads_of_callsOf u hts))).1 gfn hg vs' hsrt)
    exact ⟨r.isSome && sameResult r r', .mem hr hr'⟩
  | .exMatch ys s p t body, vars, σ, hok, hσ, hc => by
    rw [Semantics.condOK] at hok; replace hok := ((Bool.and_eq_true _ _).mp hok).1
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
    simp only [Cond.callHeadsFP, Cond.evalTermsFP, List.flatMap_cons, List.mem_append] at hc
    obtain ⟨r, hr⟩ := evalTerm_result hsc fns_headsOK hσ t hok.1.2 (fun g hg => (hc g (.inl hg)).2)
      (fun g ts hts gfn hg _ vs' _ _ hsrt => (hc g (.inl (mem_heads_of_callsOf t hts))).1 gfn hg vs' hsrt)
    cases r with
    | none => exact ⟨false, .exNone hr⟩
    | some v =>
      let g : Subst → Bool := fun σ' => decide (Holds c (vars.length + ys.length) σ' body true)
      have hb : ∀ σ', Extends c vars.length ys σ σ' → PatVal c σ' p v →
          Holds c (vars.length + ys.length) σ' body (g σ') := by
        intro σ' he _
        obtain ⟨b, hb⟩ := holds_of_callsFP hsc body hok.2 (wellSorted_extendsFP hσ he)
          (fun g hg => hc g (.inr hg))
        rw [List.length_append] at hb
        by_cases hT : Holds c (vars.length + ys.length) σ' body true
        · have : g σ' = true := decide_eq_true hT
          rw [this]; exact hT
        · have : g σ' = false := decide_eq_false hT
          rw [this]
          cases b with
          | true => exact absurd hb hT
          | false => exact hb
      exact ⟨decide (∃ σ', Extends c vars.length ys σ σ' ∧ PatVal c σ' p v ∧ g σ' = true),
        .exSome g hr hb decide_eq_true_iff⟩
  | .ex s body, vars, σ, hok, hσ, hc => by
    rw [Semantics.condOK] at hok
    let g : Subst → Bool := fun σ' => decide (Holds c (vars.length + 1) σ' body true)
    have hb : ∀ σ', Extends c vars.length [s] σ σ' → Holds c (vars.length + 1) σ' body (g σ') := by
      intro σ' he
      obtain ⟨b, hb⟩ := holds_of_callsFP hsc body hok (wellSorted_extendsFP hσ he) hc
      rw [List.length_append] at hb
      by_cases hT : Holds c (vars.length + 1) σ' body true
      · have : g σ' = true := decide_eq_true hT
        rw [this]; exact hT
      · have : g σ' = false := decide_eq_false hT
        rw [this]
        cases b with
        | true => exact absurd hb hT
        | false => exact hb
    exact ⟨decide (∃ σ', Extends c vars.length [s] σ σ' ∧ g σ' = true), .ex g hb decide_eq_true_iff⟩
  | .all s body, vars, σ, hok, hσ, hc => by
    rw [Semantics.condOK] at hok
    let g : Subst → Bool := fun σ' => decide (Holds c (vars.length + 1) σ' body true)
    have hb : ∀ σ', Extends c vars.length [s] σ σ' → Holds c (vars.length + 1) σ' body (g σ') := by
      intro σ' he
      obtain ⟨b, hb⟩ := holds_of_callsFP hsc body hok (wellSorted_extendsFP hσ he) hc
      rw [List.length_append] at hb
      by_cases hT : Holds c (vars.length + 1) σ' body true
      · have : g σ' = true := decide_eq_true hT
        rw [this]; exact hT
      · have : g σ' = false := decide_eq_false hT
        rw [this]
        cases b with
        | true => exact absurd hb hT
        | false => exact hb
    exact ⟨decide (∀ σ', Extends c vars.length [s] σ σ' → g σ' = true), .all g hb decide_eq_true_iff⟩

/-- **A function has a result at `vs` where each call in its clauses has one and each clause's
predicate has a truth value at each match.** The clauses' variables are held (`hb`), no clause of
the definition binds a variable by `\exists`. The predicate is read through `hpre` alone. -/
theorem eval_of_callsFP (hsc : SortCtx c) (hok : c.sortedOK = true) (hnoEx : c.FnsNoExs) {fn : Fn}
    (hfn : fn ∈ c.allFns) (hb : c.HeldFn fn) {vs : List GroundTerm}
    (hovl : ∀ g ∈ fn.callees, OvlTerminates c g)
    (hpre : ∀ cl ∈ fn.clauses, ∀ σ, c.WellSorted cl.vars σ → PatVals c σ cl.pats vs →
      ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hcl : ∀ cl ∈ fn.clauses, ∀ σ, PatVals c σ cl.pats vs → ∀ t, (t = cl.rhs ∨ cl.req = some t ∨ cl.ens = some t) →
      ∀ g ts, ts ∈ callsOf g t → CallOK c σ g ts) :
    ∃ r, Eval c fn.label vs r := by
  have hplain := Semantics.sortedOK_plainCl_of_noExs hok hnoEx fn hfn
  have hlook : c.lookupFn fn.label = some fn := by
    rw [Semantics.lookupFn_eq]; exact find?_label hsc.nodupFns hfn
  refine eval_resultRH hlook hplain hb
    (fun cl hcl' σ hσ hm => ⟨fun t ht => ?_, hpre cl hcl' σ hσ hm⟩)
    (fun cl hcl' σ ha => ?_) (fun cl hcl' σ ha t ht => ?_)
  · obtain ⟨-, -, L, hL, hreqs, -, -⟩ := clause_ctxOccE hok hfn hcl'
    exact evalTerm_result hsc hL hσ t (hreqs t ht) (fun g hg => hovl g (heads_req_callees hcl' ht hg))
      (hcl cl hcl' σ hm t (Or.inr (Or.inl ht)))
  · obtain ⟨-, -, L, hL, -, hrhs, -⟩ := clause_ctxOccE hok hfn hcl'
    exact evalTerm_result hsc hL ((wellSortedAt_univ (hplain cl hcl').1).mp ha.1) cl.rhs hrhs
      (fun g hg => hovl g (heads_rhs_callees hcl' hg)) (hcl cl hcl' σ ha.2.1 _ (Or.inl rfl))
  · obtain ⟨-, -, L, hL, -, -, henss⟩ := clause_ctxOccE hok hfn hcl'
    exact evalTerm_result hsc hL ((wellSortedAt_univ (hplain cl hcl').1).mp ha.1) t (henss t ht)
      (fun g hg => hovl g (heads_ens_callees hcl' ht hg)) (hcl cl hcl' σ ha.2.1 t (Or.inr (Or.inr ht)))

/-- **A function terminates where the functions its clauses apply terminate**, those of its
right-hand sides, `requires` and `ensures` (`hcall`, `hovl`) and those of its clauses' predicates
(`hpre`): each predicate, well sorted (`hpok`), then has a truth value at each match
(`holds_of_callsFP`). -/
theorem terminates_of_calleesFP (hsc : SortCtx c) (hok : c.sortedOK = true) (hnoEx : c.FnsNoExs) {fn : Fn}
    (hfn : fn ∈ c.allFns) (hb : c.HeldFn fn)
    (hcall : ∀ g ∈ fn.callees, Terminates c g) (hovl : ∀ g ∈ fn.callees, OvlTerminates c g)
    (hpre : ∀ g ∈ fn.preHeadsFP, Terminates c g ∧ OvlTerminates c g)
    (hpok : ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.pre = true) : Terminates c fn.label := by
  intro fn' hfn' vs _
  have hlook : c.lookupFn fn.label = some fn := by
    rw [Semantics.lookupFn_eq]; exact find?_label hsc.nodupFns hfn
  rw [hlook] at hfn'
  cases hfn'
  exact eval_of_callsFP hsc hok hnoEx hfn hb hovl
    (fun cl hcl σ hσ _ => holds_of_callsFP hsc cl.pre (hpok cl hcl) hσ fun g hg =>
      hpre g (List.mem_flatMap.mpr ⟨cl, hcl, hg⟩))
    (fun cl hcl _ _ t ht g ts hts gfn hg _ vs' _ _ hsrt =>
      hcall g (heads_callees hcl ht (mem_heads_of_callsOf t hts)) gfn hg vs' hsrt)

/-- The sort predicates terminate: their patterns bind their one variable, they call nothing, and
their clauses' predicate is `\top`. -/
theorem sortPreds_terminateFP (hsc : SortCtx c) (hok : c.sortedOK = true) (hnoEx : c.FnsNoExs) {fn : Fn}
    (hfn : fn ∈ c.sortPreds) : Terminates c fn.label :=
  terminates_of_calleesFP hsc hok hnoEx (List.mem_append_right _ hfn)
    (fun cl hcl => Semantics.heldAt_of_bindsRH (Semantics.sortPreds_binds hfn cl hcl))
    (by rw [sortPreds_callees hfn]; intro g hg; nomatch hg)
    (by rw [sortPreds_callees hfn]; intro g hg; nomatch hg)
    (fun g hg => by
      obtain ⟨cl, hcl, hg⟩ := List.mem_flatMap.mp hg
      rw [Semantics.sortPreds_pre hfn cl hcl] at hg
      nomatch hg)
    (fun cl hcl => by rw [Semantics.sortPreds_pre hfn cl hcl]; rfl)

/-- **Every function terminates, by an order of the functions that counts the predicates'
calls**: in a core `sortedOK` accepts, with the sort context, whose clauses' variables are held,
no clause binding a variable by `\exists` and no symbol function-overloaded, given the termination
of the functions `preRankObligationsFP` names. By induction on the position in `ord`: a function
not named applies, in its clauses' terms and predicates, sort predicates and functions placed
before it only. -/
theorem terminates_of_preRankFP (hsc : SortCtx c) (hok : c.sortedOK = true) (hnoEx : c.FnsNoExs)
    (hrh : c.RightHeld) (hfo : c.fnOvlSyms = []) (ord : List Sym)
    (hnamed : ∀ g ∈ c.preRankObligationsFP ord, Terminates c g) : ∀ f, Terminates c f := by
  have hovl : ∀ g, OvlTerminates c g := fun g => ovlTerminates_of_not_fnOvl (by rw [hfo]; exact List.not_mem_nil)
  have pos : ∀ (n : Nat) (fn : Fn), fn ∈ c.fns → ord.idxOf fn.label = n → Terminates c fn.label := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro fn hmem hn
      by_cases hN : fn.label ∈ c.preRankObligationsFP ord
      · exact hnamed _ hN
      have hrk : c.preRankedFP ord fn = true := by
        cases h : c.preRankedFP ord fn
        · exact absurd (List.mem_map.mpr ⟨fn, List.mem_filter.mpr ⟨hmem, by simp [h]⟩, rfl⟩) hN
        · rfl
      have low : ∀ g ∈ fn.callees ++ fn.preHeadsFP, Terminates c g := by
        intro g hg gfn hgfn
        obtain ⟨hgm, hlab⟩ := lookupFn_spec hgfn
        rcases List.mem_append.mp hgm with hu | hp
        · have := List.all_eq_true.mp hrk g hg
          simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
          rcases this with h | h
          · have hm : g ∈ c.fns.map (·.label) := hlab ▸ List.mem_map_of_mem hu
            rw [List.contains_iff_mem.mpr hm] at h
            cases h
          · subst hlab
            exact ih _ (hn ▸ h) gfn hu rfl gfn hgfn
        · exact hlab ▸ sortPreds_terminateFP hsc hok hnoEx hp gfn (hlab ▸ hgfn)
      exact terminates_of_calleesFP hsc hok hnoEx (List.mem_append_left _ hmem) (hrh.heldFn hmem)
        (fun g hg => low g (List.mem_append_left _ hg)) (fun g _ => hovl g)
        (fun g hg => ⟨low g (List.mem_append_right _ hg), hovl g⟩)
        (Semantics.sortedOK_preOK hok fn hmem)
  intro f fn hfn
  obtain ⟨hgm, hlab⟩ := lookupFn_spec hfn
  subst hlab
  rcases List.mem_append.mp hgm with hu | hp
  · exact pos _ fn hu rfl fn hfn
  · exact sortPreds_terminateFP hsc hok hnoEx hp fn hfn

/-! ## Totality of a function whose own clauses have the predicate `\top`

The covering check reads a clause's patterns and `requires`: a clause it counts applies wherever
its patterns match, which holds where its predicate is `\top`. So the check stays sound for a
function whose own clauses have the predicate `\top`, whatever the predicates of the other
functions' clauses. -/

/-- **The sort predicates are total**: their clauses have no `requires`, the predicate `\top` and
Bool literals as right-hand sides, and each has a clause over a variable of sort K. -/
theorem sortPreds_totalFP (hsc : SortCtx c) (hok : c.sortedOK = true) (hnoEx : c.FnsNoExs) {fn : Fn}
    (hfn : fn ∈ c.sortPreds) : Total c fn.label := by
  have hmem : fn ∈ c.allFns := List.mem_append_right _ hfn
  have hlook : c.lookupFn fn.label = some fn := by
    rw [Semantics.lookupFn_eq]; exact find?_label hsc.nodupFns hmem
  intro fn' hfn' vs hvs
  rw [hlook] at hfn'
  cases hfn'
  have hfacts : fn.args = [Srt.k] ∧ (∀ cl ∈ fn.clauses, cl.req = none ∧ ∃ s l, cl.rhs = .dv s l) ∧
      ∃ cl ∈ fn.clauses, cl.vars = [Srt.k] ∧ cl.pats = [.var 0] ∧ cl.req = none := by
    simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
      List.mem_filterMap, Option.map_eq_some_iff] at hfn
    rcases hfn with rfl | rfl | ⟨X, _, _, _, rfl⟩
    · refine ⟨rfl, fun cl hcl => ?_, { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool true), ens := none, prio := 50 },
        List.mem_singleton_self _, rfl, rfl, rfl⟩
      simp only [List.mem_singleton] at hcl
      subst hcl
      exact ⟨rfl, _, _, rfl⟩
    · refine ⟨rfl, fun cl hcl => ?_, { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 },
        by simp, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl <;> exact ⟨rfl, _, _, rfl⟩
    · refine ⟨rfl, fun cl hcl => ?_, { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 },
        by simp, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl <;> exact ⟨rfl, _, _, rfl⟩
  obtain ⟨hargs, hshape, cl₀, hcl₀, hv₀, hp₀, hr₀⟩ := hfacts
  rw [hargs] at hvs
  obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
  have hσ : c.WellSorted cl₀.vars [(0, w)] := by
    rw [hv₀]
    intro i s hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨w, lookup_cons_self _ _ _, hw⟩
    | succ i => simp at hi
  refine eval_defined hlook (Semantics.sortedOK_plainCl_of_noExs hok hnoEx fn hmem)
    (fun cl hcl => Semantics.heldAt_of_bindsRH (Semantics.sortPreds_binds hfn cl hcl))
    (fun cl hcl σ _ _ => ⟨(fun t ht => by rw [(hshape cl hcl).1] at ht; cases ht), true,
      Clause.holds_preTop (Semantics.sortPreds_pre hfn cl hcl) σ⟩)
    (fun cl hcl _ _ => by obtain ⟨_, s, l, h⟩ := hshape cl hcl; rw [h]; exact ⟨_, EvalTerm.dv⟩)
    ⟨cl₀, hcl₀, hr₀, [(0, w)], hσ.at _, by rw [hp₀]; exact .cons (.var (lookup_cons_self _ _ _)) .nil,
      (fun t ht => by rw [hr₀] at ht; cases ht), Clause.holds_preTop (Semantics.sortPreds_pre hfn cl₀ hcl₀) _⟩ (sortPreds_ens hfn)

/-- **A function whose clauses are total is total, its own clauses' predicate `\top`** (`hclk`):
its right-hand sides are total over `tot`, whose functions but itself are total; its self calls
decrease; its covering rows cover its argument sorts. Every function terminates (`hterm`); nothing
is asked of the predicates of the other functions' clauses. -/
theorem total_of_partsFP (hsc : SortCtx c) (hok : c.sortedOK = true) (hnoEx : c.FnsNoExs)
    (hs : c.shapesOK = true) (hterm : ∀ g, Terminates c g)
    {fn : Fn} (hfn : fn ∈ c.allFns) (hb : c.HeldFn fn)
    (hclk : ∀ cl ∈ fn.clauses, sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args ∧ cl.pre = .top)
    {dec : Option Nat} (hdec : decreasingOK c fn dec = true) {n : Nat}
    (hcov : c.covers n fn.args (Semantics.coverRows fn) = true) {tot : List Sym}
    (hrhs : ∀ cl ∈ fn.clauses, c.totalTerm tot cl.rhs = true)
    (hnoens : ∀ cl ∈ fn.clauses, cl.ens = none)
    (htot : ∀ g ∈ tot, g ≠ fn.label → Total c g) : Total c fn.label := by
  have hlook : c.lookupFn fn.label = some fn := by
    rw [Semantics.lookupFn_eq]; exact find?_label hsc.nodupFns hfn
  have hplain := Semantics.sortedOK_plainCl_of_noExs hok hnoEx fn hfn
  intro fn' hfn' vs hvs
  rw [hlook] at hfn'
  cases hfn'
  suffices h : ∀ m vs, c.sortsOf vs = some fn.args → decMeasure dec vs < m →
      ∃ v, Eval c fn.label vs (some v) from h _ vs hvs (Nat.lt_succ_self _)
  intro m
  induction m with
  | zero => intro _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro vs hvs hlt
    refine eval_defined hlook hplain hb (fun cl hcl σ hσ _ => ⟨fun t ht => ?_, true,
        Clause.holds_preTop (hclk cl hcl).2 σ⟩)
      (fun cl hcl σ ha => ?_) ?_ hnoens
    · obtain ⟨-, -, L, hL, hreqs, -, -⟩ := clause_ctxOccE hok hfn hcl
      exact evalTerm_result hsc hL hσ t (hreqs t ht) (fun _ _ _ _ kg _ _ => hterm kg.name)
        fun g _ _ gfn hg _ vs' _ _ hsrt => hterm g gfn hg vs' hsrt
    · obtain ⟨-, -, L, hL, -, hrs, -⟩ := clause_ctxOccE hok hfn hcl
      refine evalTerm_defined hsc hs hL ((wellSortedAt_univ (hplain cl hcl).1).mp ha.1) cl.rhs hrs (hrhs cl hcl)
        fun g ts hts hgt gfn hg vs' hts' hsrt => ?_
      by_cases hgl : g = fn.label
      · subst hgl
        rw [hlook] at hg
        cases hg
        obtain ⟨i, j, p, rfl, hti, hpi, hsi⟩ := decreasingOK_clause hdec hcl (Or.inl rfl) hts
        obtain ⟨v, hvi, hpv⟩ := patVals_get ha.2.1 hpi
        obtain ⟨w, hw, hwv⟩ := strictlyIn_size p hpv hsi
        have hvi' : vs'[i]? = some w := (evalTerms_var hts' hti (allSome_map_some vs')).trans hw
        refine ih vs' hsrt ?_
        have h1 : decMeasure (some i) vs' = w.size := by simp [decMeasure, hvi']
        have h2 : decMeasure (some i) vs = v.size := by simp [decMeasure, hvi]
        omega
      · exact htot g (List.contains_iff_mem.mp hgt) hgl gfn hg vs' hsrt
    · have htyped : ∀ r ∈ Semantics.coverRows fn, ∃ vars, RowTyped c vars fn.args r := by
        intro r hr
        obtain ⟨cl, hcl, _, _, rfl⟩ := mem_coverRows hr
        exact ⟨cl.vars, rowTyped_of_sorts (hclk cl hcl).1⟩
      obtain ⟨r, hr, hm⟩ := covers_sound n fn.args _ hcov htyped vs hvs
      obtain ⟨cl, hcl, hreq, hnd, rfl⟩ := mem_coverRows hr
      exact ⟨cl, hcl, hreq, applies_of_rowRH (hb cl hcl) (hclk cl hcl).1 hreq (hclk cl hcl).2 hnd hvs hm⟩

/-- **A function `totalOK` confirms is total, its own clauses' predicate `\top`** (`hpt`), in a
core `coreOK` accepts whose functions terminate, the total functions before it total. The other
functions' clauses may have a predicate. -/
theorem total_of_totalOKFP (h : c.coreOK = true) (hnoEx : c.FnsNoExs) (hterm : ∀ g, Terminates c g)
    {fn : Fn} (hfn : fn ∈ c.fns) (hb : c.HeldFn fn) (hT : c.totalOK fn = true)
    (hpt : ∀ cl ∈ fn.clauses, cl.pre = .top) (htot : ∀ g ∈ c.totalBefore fn, Total c g) :
    Total c fn.label := by
  obtain ⟨hok, -, -, hp, hids⟩ := Semantics.coreOK_parts h
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)
  have hsc := sortCtx_of_all hok hsr (Semantics.ovlCase_of_core h)
  simp only [Semantics.totalOK, Bool.and_eq_true, List.all_eq_true] at hT
  obtain ⟨⟨⟨⟨hs, hdec⟩, hcov⟩, hrhs⟩, hne⟩ := hT
  have hfok : ∀ cl ∈ fn.clauses, c.clauseSorted fn (c.fns.map Fn.sig) cl = true := by
    replace hok := Semantics.sortedOK_sorted hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.1.2 fn hfn
  refine total_of_partsFP hsc hok hnoEx hs hterm (List.mem_append_left _ hfn) hb (fun cl hcl => ?_) hdec
    (n := Semantics.coverFuel fn) hcov hrhs (fun cl hcl => by simpa using hne cl hcl) (fun g hg hgl => ?_)
  · have := hfok cl hcl
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
    replace this := this.1
    exact ⟨sortsOfTerms_all_of_nf this.1.1.1.1.1, hpt cl hcl⟩
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨p, hp, rfl⟩) | hg
    · exact htot g hg
    · exact sortPreds_totalFP hsc hok hnoEx hp
    · exact absurd hg hgl

/-! ## `FnHyp` -/

/-- **`FnHyp` of a semantics whose clauses may have a predicate in the premise**, from `coreOK`,
`RightHeld`, no symbol function-overloaded, an order `ord` of the functions and the facts the
deciders leave: the termination of the functions `preRankObligationsFP` names (those applying, in
a clause's terms or predicate, a function not placed before them), the totality of the `[total]`
functions, the agreements `agreeObligationsI` names, the match independences `matchObligationsL`
names, and `OpenDecided` and `OpenLaws`. Each clause's predicate is then decided at each match
(`holds_of_callsFP`); nothing asks it to be `\top`. -/
theorem fnHyp_of_decidedPre (h : c.coreOK = true) (hrh : c.RightHeld) (hfo : c.fnOvlSyms = [])
    (ord : List Sym) (hterm : ∀ g ∈ c.preRankObligationsFP ord, Terminates c g)
    (htot : ∀ fn ∈ c.fns, fn.total = true → Total c fn.label)
    (hag : ∀ f ∈ c.agreeObligationsI, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn)
    (hmo : MatchObligationsL c) (hod : OpenDecided c) (hol : OpenLaws c)
    (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel)) | exact Semantics.fnsNoExs_of_all rfl) :
    FnHyp c := by
  obtain ⟨hok, -, hha, hp, hids⟩ := Semantics.coreOK_parts h
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts h).2.1) (Semantics.coreOK_ovls h)
  have hsc := sortCtx_of_all hok hsr (Semantics.ovlCase_of_core h)
  have hT := terminates_of_preRankFP hsc hok hnoEx hrh hfo ord hterm
  have hmc : Exec.MatchCtxO c := ⟨NamesApart.subsorts_trans_of hids hok,
    NamesApart.subsorts_irrefl_of hids hok, NamesApart.patHooks_of hha hids, Semantics.coreOK_ovls h⟩
  have hagA := clausesAgree_of_IO hok hnoEx hsr hmc hag
  have hmi := matchIndependentAll_of_L hok hnoEx hmc hmo
  refine ⟨fun fn hfn vs hvs => ?_, fun fn hfn ht vs hvs => ?_, hagA, fun fn hfn cl hcl => ?_, hod, hol⟩
  · exact hT fn.label fn (lookupFn_of_core h hfn) vs hvs
  · exact htot fn hfn ht fn (lookupFn_of_core h hfn) vs hvs
  · exact hmi fn.label fn (lookupFn_of_core h hfn) cl hcl

/-- `fnHyp_of_decidedPre` for an interpretation H of the parameters, of a semantics without an open
generator (`hr`): `coreOK`, `RightHeld`, the order's named functions and the function-overloaded
symbols are the data's; the facts are stated for the interpretation. -/
theorem fnHyp_of_decidedPre_withHooks (h : c.coreOK = true) (hrh : c.RightHeld) (hfo : c.fnOvlSyms = [])
    (H : HookParams) (ord : List Sym)
    (hterm : ∀ g ∈ c.preRankObligationsFP ord, Terminates (c.withHooks H) g)
    (htot : ∀ fn ∈ c.fns, fn.total = true → Total (c.withHooks H) fn.label)
    (hag : ∀ f ∈ c.agreeObligationsI, ∀ fn, (c.withHooks H).lookupFn f = some fn → ClausesAgree (c.withHooks H) fn)
    (hmo : MatchObligationsL (c.withHooks H)) (hod : OpenDecided (c.withHooks H)) (hol : OpenLaws (c.withHooks H))
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel)
    (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact Semantics.fnsNoExs_of_all rfl) :
    FnHyp (c.withHooks H) :=
  fnHyp_of_decidedPre ((Semantics.coreOK_withHooks c H).trans h) (Semantics.rightHeld_withHooks hrh H hr)
    hfo ord hterm htot (by rw [Det.Semantics.agreeObligationsI_withHooks]; exact hag) hmo hod hol
    (hnoEx := (Semantics.fnsNoExs_withHooks _ _).mpr hnoEx)

end KCore
