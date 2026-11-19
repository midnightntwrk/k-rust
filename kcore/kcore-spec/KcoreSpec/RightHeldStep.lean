/-
  KCore. The evaluations a step reads have results (`StepDecided`), for a semantics whose clauses'
  patterns need not bind every variable, with no hypothesis on the sorts of the variables the
  patterns and conditions do not hold.

  `Semantics.sortedOKCl` (SortedCl.lean) is `sortedOK` with each clause asked `clauseSortedOpen` (each variable
  occurs in the clause) and `clausePlainOpen` (an open condition variable is of a confined sort, or
  the conditions are closed) in place of `clauseSorted` and `clausesPlain`; `sortedOK` gives it
  where no clause binds a variable by `\exists` (`Semantics.sortedOKCl_of_sortedOK_noExs`). Of the clauses, `StepDecided` reads only that every function
  has a result at arguments of its sorts (`FnTerminates`) and that the right sides are well sorted
  (`SortCtx`, `sortCtx_of_allCl`): a well-sorted term has a result under a well-sorted substitution
  (`Model.evalTerm_totalCl`), and a rule's conditions and right side are well sorted
  (`rule_ctxCl`, `rule_ctx_ensCl`), its predicates `\top`. This is `stepDecided_of_coreCl`;
  `stepDecided_of_fnHypCl` takes `FnTerminates` from `FnHyp`.
-/
import KcoreSpec.FaithfulCompleteAt
import KcoreSpec.OpenClause
import KcoreSpec.HoldsDecided

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

variable {c : Semantics}

/-- **A sort predicate terminates** at every argument list (`sortPred_total`), from `SortCtx`. -/
theorem sortPred_totalCl (hsc : SortCtx c) {fn : Fn} (hfn : fn ∈ c.sortPreds) (vs : List GroundTerm) :
    ∃ r, Eval c fn.label vs r := by
  have hlk : c.lookupFn fn.label = some fn := by
    rw [Semantics.lookupFn_eq]; exact find?_label hsc.nodupFns (List.mem_append_right _ hfn)
  have hsh := sortPreds_shape hfn
  exact eval_result hlk (fun cl hcl => ⟨Semantics.sortPreds_exs hfn cl hcl, Semantics.sortPreds_post hfn cl hcl⟩) (Semantics.sortPreds_binds hfn) (fun cl hcl σ _ _ => ⟨(fun t ht => by rw [(hsh cl hcl).1] at ht; cases ht), true,
      Clause.holds_preTop (Semantics.sortPreds_pre hfn cl hcl) σ⟩)
    (fun cl hcl _ _ => by obtain ⟨_, s, l, h⟩ := hsh cl hcl; rw [h]; exact ⟨_, .dv⟩)
    (fun cl hcl _ _ t ht => by rw [sortPreds_ens hfn cl hcl] at ht; cases ht)

/-- A function of the semantics terminates at arguments of its sorts, where every user function
does (`fn_total`), from `SortCtx`. -/
theorem fn_totalCl (hsc : SortCtx c) (ht : FnTerminates c) {fn : Fn} (hfn : fn ∈ c.allFns) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some fn.args) : ∃ r, Eval c fn.label vs r := by
  rcases List.mem_append.mp hfn with hfn | hfn
  · exact ht fn hfn vs hvs
  · exact sortPred_totalCl hsc hfn vs

mutual
  /-- **Every well-sorted term has a result** under a well-sorted σ, where every function of the
  definition has a result at arguments of its sorts (`evalTerm_total`), from `SortCtx` and `OvlOK`. -/
  theorem evalTerm_totalCl (hsc : SortCtx c) (hov : OvlOK c) (hft : FnTerminates c) {L : List CtorSig}
      (hL : HeadsOK c L) {vars : List Srt} {σ : Subst} (hσ : c.WellSorted vars σ) : ∀ {t : Term} {s : Srt},
      sortOfTerm (c.rhsCtx L) vars t = some s → ∃ r, EvalTerm c σ t r
    | .var _, _, _ => ⟨_, .var⟩
    | .dv _ _, _, _ => ⟨_, .dv⟩
    | .inj _ _ t, _, ht => by
      obtain ⟨-, ht', -⟩ := sortOfTerm_inj.mp ht
      obtain ⟨r, hr⟩ := evalTerm_totalCl hsc hov hft hL hσ ht'
      exact ⟨_, .inj hr⟩
    | .as _ _, _, ht => absurd ht sortOfTerm_rhs_as
    | .app f ts, _, ht => by
      obtain ⟨k, hk, hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
      obtain ⟨rs, hrs⟩ := evalTerms_totalCl hsc hov hft hL hσ hargs
      by_cases hc : c.isCtor f = true
      · exact ⟨_, .ctor hc hrs⟩
      have hc' : c.isCtor f = false := by simpa using hc
      by_cases hh : isHook f = true
      · cases has : allSome rs with
        | none => exact ⟨none, .hook hc' hh hrs (fun ws hw => by rw [has] at hw; cases hw) (fun _ => rfl)⟩
        | some ws =>
          obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hh ws
          exact ⟨o, .hook hc' hh hrs (fun ws' hw => by rw [has] at hw; cases hw; exact ho)
            (fun hn => by rw [has] at hn; cases hn)⟩
      have hh' : isHook f = false := by simpa using hh
      by_cases hp : c.isParam f = true
      · exact ⟨_, .param hc' hh' hp hrs rfl⟩
      have hp' : c.isParam f = false := by simpa using hp
      cases hovf : c.isOvl f with
      | true =>
        obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc hL hk hovf
        exact EvalTerm.ovl_result (hov.hyp hsc.trans).fnFacts hc' hovf hrs hlo
          (fun ws has => EvalTerms.sorted hsc hrs hL hσ hargs has)
          (fun kg _ _ fn hfn _ hn vs hvs => hn ▸ hft fn hfn vs hvs)
      | false =>
      cases has : allSome rs with
      | none => exact ⟨none, .callUndef hc' hh' hrs has hp'⟩
      | some ws =>
        subst hkn
        obtain ⟨fn, hfn, rfl⟩ := rhsHead_fn hov.ok hL hkm hc' hh' hp' hovf
        have hws : c.sortsOf ws = some fn.args := EvalTerms.sorted hsc hrs hL hσ hargs has
        obtain ⟨r, hr⟩ := fn_totalCl hsc hft hfn hws
        exact ⟨r, .call hc' hh' hrs has hr hp'⟩
    termination_by structural t _ _ => t
  theorem evalTerms_totalCl (hsc : SortCtx c) (hov : OvlOK c) (hft : FnTerminates c) {L : List CtorSig}
      (hL : HeadsOK c L) {vars : List Srt} {σ : Subst} (hσ : c.WellSorted vars σ) : ∀ {ts : List Term} {ss : List Srt},
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → ∃ rs, EvalTerms c σ ts rs
    | [], _, _ => ⟨[], .nil⟩
    | t :: ts, _, hs => by
      obtain ⟨s, ss', h1, h2, -⟩ := sortsOfTerms_cons.mp hs
      obtain ⟨r, hr⟩ := evalTerm_totalCl hsc hov hft hL hσ h1
      obtain ⟨rs, hrs⟩ := evalTerms_totalCl hsc hov hft hL hσ h2
      exact ⟨r :: rs, .cons hr hrs⟩
    termination_by structural ts _ _ => ts
end

end Model

variable {c : Semantics}

/-- **Every configuration is `StepDecided`** where every function has a result at arguments of its
sorts, for a semantics `sortedOKCl` and `srReady` accept whose overloading
symbols are as `Γ`'s readings take them: no fact on the clauses beyond their right sides' sorts. -/
theorem stepDecided_of_coreCl (hok : c.sortedOKCl = true) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) (hsr : c.srReady = true) (hov : OvlOK c)
    (hft : FnTerminates c) (x : GroundTerm) : StepDecided c x := by
  have hsc := sortCtx_of_allCl hok hsr (OvlOK.ovlCase hov)
  intro r hr _
  obtain ⟨-, hreqs, hrhss⟩ := rule_ctxCl hok hr
  obtain ⟨hpre, hpost⟩ := htop _ hr
  have hensS := rule_ctx_ensCl hok hr
  refine ⟨fun σ hσ _ => ⟨fun t ht => Model.evalTerm_totalCl hsc hov hft fns_headsOK (Rule.wellSorted_of_at (hb r hr) hσ)
      (hreqs t ht), true, hpre ▸ .top⟩,
    fun σ hσ _ _ _ => ⟨Model.evalTerm_totalCl hsc hov hft fns_headsOK hσ hrhss,
      fun e he => Model.evalTerm_totalCl hsc hov hft fns_headsOK hσ (hensS e he), true, hpost ▸ .top⟩⟩

end Faithful

open Faithful

/-- **`stepDecided_of_fnHyp` with the clauses asked `clauseSortedOpen` and `clausePlainOpen`** (in
`sortedOKCl`) in place of `sortedOK`'s clause conjuncts, and no fact on the sorts of the variables
their patterns and conditions do not hold. -/
theorem stepDecided_of_fnHypCl {c : Semantics} (hok : c.sortedOKCl = true) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) (hsr : c.srReady = true) (hov : OvlOK c)
    (hf : FnHyp c) (x : Config c) : StepDecided c x.val :=
  stepDecided_of_coreCl hok hb htop hsr hov hf.1 x.val

end KCore
