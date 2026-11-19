/-
  kore.k's walk of a function's clauses, read backwards: one inversion per function of the walk,
  on kore.k's semantics read from its kompiled text (`c₀`).

  The functions are `apply`, `applyL`, `result`, `evalAt`, `evalIf`, `tryAt`, `orElse`, `tryCl`,
  `tryM`. Their clauses are the semantics' own, as literals tied to `lookupFn` by the kernel
  (`tryMDef_ksc` …). Every clause is at priority 50, with no ensures, existential variable or
  predicate, so a call is either one clause whose patterns match, whose `requires` holds and whose
  right side gives the result, or every clause fails and the result is none
  (`byClause_cases_ksc`). A failing clause whose patterns match has a `requires` that is not true
  there (`FailsR.req_ksc`).

  The inversions (`result_inv_ksc`, …, `tryM_inv_ksc`) are over a relation `R` at the calls that
  implies kore.k's evaluation, so that the helpers they call (`hasBot`, `lookup`, `nextCl`,
  `cprio`, `subsOf`, `matchTs`, `inst`) have their one value (`F.eval_iff`): a `requires` built of
  helpers only is read by comparing it with its forward evaluation (`EvalTermR.helper_val_ksc`).
  `tryM`'s `requires` holds a call of `eval`: `reqEq_inv_ksc` (`==K`, `try-holds`) and
  `reqNe_inv_ksc` (`=/=K`, `try-refuted`) read the instance it is called at and give the requires'
  value from what `eval` gives.

  The priorities: `nextClF` and `nextRlF` give the least priority above their bound
  (`leastOver_spec_ksc`, `nextClF_spec_ksc`, `nextRlF_spec_ksc`), so
  the walk's first priority leaves nothing below it (`below_first_ksc`), and from "every clause
  below `P` fails" and "every clause at `P` fails" the next priority has every clause below it fail
  (`below_next_ksc`).

  `tryM_undef_ksc` is the evaluation that shows a binding without an entry for the right side's
  variable gives `tryM` the result none: `tryM(D, bv(true), vr(0), m(.Bind, .Ms))` has the result
  none, `inst(vr(0), .Bind)` having no value.
-/
import User.SpecTerms
import User.ColMatchEval

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## The clauses, as the semantics holds them -/

namespace WalkV
open _root_.KK Terms

/-- The `requires` of `try-holds` (`g = 29`, `==K`) and `try-refuted` (`g = 30`, `=/=K`):
`eval(D, inst(Req, B)) ==K bv(true)` with `D`, `Req`, `B` the variables `i`, `j`, `k`. -/
abbrev reqT_ksc (g : Sym) (i j k : Nat) : Term :=
  .app g [.app 0 [.inj 33 1 (.app 464 [.var i, .app 476 [.var j, .var k]]), .app 1 []],
    .app 0 [.inj 33 1 (.app 413 [.dv 2 (.bool true)]), .app 1 []]]

/-- `tryM` (514): `try-refuted`, `try-holds`, `try-nomatch`. -/
def tryMDef_ksc : Fn :=
  { label := 514, args := [45, 33, 33, 37], result := 41, total := false, clauses := [
    plainCl [45, 33, 33, 46, 37] [.var 0, .var 1, .var 2, .app 428 [.var 3, .var 4]]
      (.app 514 [.var 0, .var 1, .var 2, .var 4]) (req := some (reqT_ksc 30 0 1 3)),
    plainCl [45, 33, 33, 46, 37] [.var 0, .var 1, .var 2, .app 428 [.var 3, .var 4]]
      (.app 439 [.app 464 [.var 0, .app 476 [.var 2, .var 3]]]) (req := some (reqT_ksc 29 0 1 3)),
    plainCl [45, 33, 33] [.var 0, .var 1, .var 2, .app 403 []] (.app 433 [])] }

/-- `tryCl` (513): `try`. -/
def tryClDef_ksc : Fn :=
  { label := 513, args := [45, 43, 33, 33, 43], result := 41, total := false, clauses := [
    plainCl [45, 43, 33, 33, 43] [.var 0, .var 1, .var 2, .var 3, .var 4]
      (.app 514 [.var 0, .var 2, .var 3, .app 489 [.var 1, .var 4, .app 400 [], .app 509 [.var 0]]])] }

/-- `tryAt` (512): `ta-take`, `ta-skip`, `ta-nil`. -/
def tryAtDef_ksc : Fn :=
  { label := 512, args := [45, 43, 35, 3], result := 41, total := false, clauses := [
    plainCl [45, 43, 3, 2, 43, 33, 33, 35, 3]
      [.var 0, .var 1, .app 415 [.var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .var 8]
      (.app 497 [.app 513 [.var 0, .var 4, .var 5, .var 6, .var 1], .var 0, .var 1, .var 7, .var 8])
      (req := some (.app 23 [.app 460 [.var 2, .var 3], .var 8])),
    plainCl [45, 43, 3, 2, 43, 33, 33, 35, 3]
      [.var 0, .var 1, .app 415 [.var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .var 8]
      (.app 512 [.var 0, .var 1, .var 7, .var 8])
      (req := some (.app 24 [.app 460 [.var 2, .var 3], .var 8])),
    plainCl [45, 43, 3] [.var 0, .var 1, .app 401 [], .var 2] (.app 433 [])] }

/-- `orElse` (497): `else-some`, `else-none`. -/
def orElseDef_ksc : Fn :=
  { label := 497, args := [41, 45, 43, 35, 3], result := 41, total := false, clauses := [
    plainCl [33, 41, 45, 43, 35, 3] [.as (.app 439 [.var 0]) 1, .var 2, .var 3, .var 4, .var 5] (.var 1),
    plainCl [45, 43, 35, 3] [.app 433 [], .var 0, .var 1, .var 2, .var 3]
      (.app 512 [.var 0, .var 1, .var 2, .var 3])] }

/-- `result` (502): `result-none`, `result-some`. -/
def resultDef_ksc : Fn :=
  { label := 502, args := [3, 43, 41], result := 33, total := false, clauses := [
    plainCl [3, 43] [.var 0, .var 1, .app 433 []] (.app 412 []),
    plainCl [3, 43, 33] [.var 0, .var 1, .app 439 [.var 2]] (.var 2)] }

/-- `evalAt` (465): `ea-at`, `ea-none`. -/
def evalAtDef_ksc : Fn :=
  { label := 465, args := [45, 43, 35, 36], result := 41, total := false, clauses := [
    plainCl [45, 43, 35, 3] [.var 0, .var 1, .var 2, .app 410 [.var 3]]
      (.app 466 [.var 0, .var 1, .var 2, .var 3, .app 512 [.var 0, .var 1, .var 2, .var 3]]),
    plainCl [45, 43, 35] [.var 0, .var 1, .var 2, .app 431 []] (.app 433 [])] }

/-- `evalIf` (466): `ei-next`, `ei-some`. -/
def evalIfDef_ksc : Fn :=
  { label := 466, args := [45, 43, 35, 3, 41], result := 41, total := false, clauses := [
    plainCl [45, 43, 35, 3] [.var 0, .var 1, .var 2, .var 3, .app 433 []]
      (.app 465 [.var 0, .var 1, .var 2, .app 495 [.var 2, .app 410 [.var 3]]]),
    plainCl [45, 43, 35, 3, 33, 41] [.var 0, .var 1, .var 2, .var 3, .as (.app 439 [.var 4]) 5] (.var 5)] }

theorem tryMDef_lookup_ksc : c₀.lookupFn 514 = some tryMDef_ksc := by kernel_rfl
theorem tryClDef_lookup_ksc : c₀.lookupFn 513 = some tryClDef_ksc := by kernel_rfl
theorem tryAtDef_lookup_ksc : c₀.lookupFn 512 = some tryAtDef_ksc := by kernel_rfl
theorem orElseDef_lookup_ksc : c₀.lookupFn 497 = some orElseDef_ksc := by kernel_rfl
theorem resultDef_lookup_ksc : c₀.lookupFn 502 = some resultDef_ksc := by kernel_rfl
theorem evalAtDef_lookup_ksc : c₀.lookupFn 465 = some evalAtDef_ksc := by kernel_rfl
theorem evalIfDef_lookup_ksc : c₀.lookupFn 466 = some evalIfDef_ksc := by kernel_rfl

end WalkV

/-! ## Inverting a call -/

section Inv
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms

variable {R : CallRel}

/-- **A call of a function whose clauses have no ensures and no existential variable**: a clause
whose patterns match under a well-sorted substitution, whose `requires` (if any) is true and whose
right side has the result; or every clause fails and the result is none. -/
theorem byClause_cases_ksc {f : Sym} {fn : Fn} {vs : List GroundTerm} {r : Option GroundTerm}
    (hb : ByClause c₀ R f vs r) (hfn : c₀.lookupFn f = some fn)
    (hpl : ∀ cl ∈ fn.clauses, cl.ens = none ∧ cl.exs = []) :
    (∃ cl ∈ fn.clauses, ∃ σ, c₀.WellSorted cl.vars σ ∧ PatVals c₀ σ cl.pats vs ∧
        (∀ t, cl.req = some t → EvalTermR c₀ R σ t (some (bool true))) ∧ EvalTermR c₀ R σ cl.rhs r) ∨
      (r = none ∧ ∀ cl ∈ fn.clauses, FailsR c₀ R vs cl) := by
  cases hb with
  | clause hfn' hmem hσ hmatch hreq _ _ _ hrhs _ _ =>
    rw [hfn] at hfn'; cases hfn'
    exact .inl ⟨_, hmem, _, hσ, hmatch, hreq, hrhs⟩
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    exact .inr ⟨rfl, hnone⟩
  | ensFails hfn' hmem _ _ _ _ _ _ ht =>
    rw [hfn] at hfn'; cases hfn'
    rw [(hpl _ hmem).1] at ht; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (hpl _ hmem).2 hne
  | exNone hfn' hmem hne =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (hpl _ hmem).2 hne

/-- **A failing clause whose patterns match**, with the predicate `⊤`: its `requires` is not true
there. -/
theorem FailsR.req_ksc {vs : List GroundTerm} {cl : Clause} (h : FailsR c₀ R vs cl)
    (hpre : cl.pre = .top) {σ : Subst} (hσ : c₀.WellSorted cl.vars σ)
    (hp : PatVals c₀ σ cl.pats vs) :
    ∃ t r, cl.req = some t ∧ EvalTermR c₀ R σ t r ∧ r ≠ some (bool true) := by
  cases h with
  | intro h =>
    cases h σ (hσ.at _) hp with
    | intro ht he hr => exact ⟨_, _, ht, he, hr⟩
    | pre hf => rw [hpre] at hf; cases hf

/-- A term built of helpers only has under `R` the value its forward evaluation gives, where `R`
implies kore.k's evaluation. -/
theorem EvalTermR.helper_val_ksc (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {σ : Subst} {t : Term}
    {r v : Option GroundTerm} (h : EvalTermR c₀ R σ t r) (hv : EvalTerm c₀ σ t v) : r = v :=
  EvalTerm.functional _root_.KK.coherent (h.toEval hR) hv

/-- Variables with the listed values. -/
inductive VarsAre_ksc (σ : Subst) : List Term → List GroundTerm → Prop where
  | nil : VarsAre_ksc σ [] []
  | cons {i : Nat} {ts : List Term} {v : GroundTerm} {vs : List GroundTerm}
      (h : σ.lookup i = some v) (hs : VarsAre_ksc σ ts vs) : VarsAre_ksc σ (.var i :: ts) (v :: vs)

theorem VarsAre_ksc.evalR {σ : Subst} {ts : List Term} {vs : List GroundTerm}
    (hv : VarsAre_ksc σ ts vs) : ∀ {rs : List (Option GroundTerm)}, EvalTermsR c₀ R σ ts rs →
    rs = vs.map some := by
  induction hv with
  | nil => intro rs h; cases h; rfl
  | cons hi _ ih =>
    intro rs h
    cases h with
    | cons h0 hs => rw [EvalTermR.var_inv_kst h0, hi, ih hs]; rfl

/-- The results of terms ending in one more term. -/
theorem EvalTermsR.snoc_inv_ksc {σ : Subst} {t : Term} : ∀ {ts : List Term}
    {rs : List (Option GroundTerm)}, EvalTermsR c₀ R σ (ts ++ [t]) rs →
    ∃ rs₁ q, rs = rs₁ ++ [q] ∧ EvalTermsR c₀ R σ ts rs₁ ∧ EvalTermR c₀ R σ t q
  | [], rs, h => by
    rcases h with _ | ⟨e0, _ | _⟩
    exact ⟨[], _, rfl, .nil, e0⟩
  | u :: ts, rs, h => by
    cases h with
    | cons h0 hs =>
      obtain ⟨rs₁, q, rfl, h1, h2⟩ := EvalTermsR.snoc_inv_ksc hs
      exact ⟨_ :: rs₁, q, rfl, .cons h0 h1, h2⟩

theorem allSome_snoc_ksc (q : Option GroundTerm) : ∀ (vs : List GroundTerm),
    allSome (vs.map some ++ [q]) = q.map fun y => vs ++ [y]
  | [] => by cases q <;> rfl
  | v :: vs => by
    simp only [List.map_cons, List.cons_append, allSome, Option.bind_some, allSome_snoc_ksc q vs]
    cases q <;> rfl

theorem allSome_cons_ksc (q : Option GroundTerm) (vs : List GroundTerm) :
    allSome (q :: vs.map some) = q.map fun y => y :: vs := by
  cases q <;> simp [allSome, _root_.KCore.allSome_map_some]

/-- A call of a function at variables with values. -/
theorem EvalTermR.callVars_ksc {σ : Subst} {g : Sym} {ts : List Term} {vs : List GroundTerm}
    {r : Option GroundTerm} (hc : c₀.isCtor g = false) (hh : isHook g = false)
    (hp : c₀.isParam g = false) (ho : c₀.isOvl g = false) (hv : VarsAre_ksc σ ts vs)
    (h : EvalTermR c₀ R σ (.app g ts) r) : R g vs r := by
  obtain ⟨rs, hts, hcase⟩ := EvalTermR.call_inv_kst hc hh hp ho h
  rw [hv.evalR hts, _root_.KCore.allSome_map_some] at hcase
  rcases hcase with ⟨vs', hvs, hR⟩ | ⟨hn, -⟩
  · cases hvs; exact hR
  · cases hn

/-- A call of a function at variables with values and one more term. -/
theorem EvalTermR.callVarsT_ksc {σ : Subst} {g : Sym} {ts : List Term} {t : Term}
    {vs : List GroundTerm} {r : Option GroundTerm} (hc : c₀.isCtor g = false)
    (hh : isHook g = false) (hp : c₀.isParam g = false) (ho : c₀.isOvl g = false)
    (hv : VarsAre_ksc σ ts vs) (h : EvalTermR c₀ R σ (.app g (ts ++ [t])) r) :
    ∃ q, EvalTermR c₀ R σ t q ∧ ((∃ y, q = some y ∧ R g (vs ++ [y]) r) ∨ (q = none ∧ r = none)) := by
  obtain ⟨rs, hts, hcase⟩ := EvalTermR.call_inv_kst hc hh hp ho h
  obtain ⟨rs₁, q, rfl, h1, h2⟩ := EvalTermsR.snoc_inv_ksc hts
  rw [hv.evalR h1, allSome_snoc_ksc] at hcase
  refine ⟨q, h2, ?_⟩
  cases q with
  | none =>
    rcases hcase with ⟨_, hvs, -⟩ | ⟨-, hr⟩
    · cases hvs
    · exact .inr ⟨rfl, hr⟩
  | some y =>
    rcases hcase with ⟨_, hvs, hR⟩ | ⟨hn, -⟩
    · cases hvs; exact .inl ⟨y, rfl, hR⟩
    · cases hn

/-- A call of a function at one term and then variables with values. -/
theorem EvalTermR.callTVars_ksc {σ : Subst} {g : Sym} {t : Term} {ts : List Term}
    {vs : List GroundTerm} {r : Option GroundTerm} (hc : c₀.isCtor g = false)
    (hh : isHook g = false) (hp : c₀.isParam g = false) (ho : c₀.isOvl g = false)
    (hv : VarsAre_ksc σ ts vs) (h : EvalTermR c₀ R σ (.app g (t :: ts)) r) :
    ∃ q, EvalTermR c₀ R σ t q ∧ ((∃ y, q = some y ∧ R g (y :: vs) r) ∨ (q = none ∧ r = none)) := by
  obtain ⟨rs, hts, hcase⟩ := EvalTermR.call_inv_kst hc hh hp ho h
  cases hts with
  | cons h0 hs =>
    rename_i q rs'
    rw [hv.evalR hs, allSome_cons_ksc] at hcase
    refine ⟨q, h0, ?_⟩
    cases q with
    | none =>
      rcases hcase with ⟨_, hvs, -⟩ | ⟨-, hr⟩
      · cases hvs
      · exact .inr ⟨rfl, hr⟩
    | some y =>
      rcases hcase with ⟨_, hvs, hR⟩ | ⟨hn, -⟩
      · cases hvs; exact .inl ⟨y, rfl, hR⟩
      · cases hn

/-- An application of an interpreted symbol under `R`: the arguments' results and what `hookRes`
gives them. -/
theorem EvalTermR.hook_inv_ksc {σ : Subst} {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c₀.isCtor f = false) (hh : isHook f = true) (h : EvalTermR c₀ R σ (.app f ts) r) :
    ∃ rs, EvalTermsR c₀ R σ ts rs ∧ (∀ vs, allSome rs = some vs → c₀.hookRes f vs = some r) ∧
      (allSome rs = none → r = none) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | hook _ _ hts hh' hund => cases ht; exact ⟨_, hts, hh', hund⟩
  | param _ h _ _ _ => cases ht; rw [hh] at h; cases h
  | call _ h _ _ _ _ => cases ht; rw [hh] at h; cases h
  | callUndef _ h _ _ _ => cases ht; rw [hh] at h; cases h
  | ovl _ ho _ => cases ht; rw [(c₀.isOvl_parts ho).2.1] at hh; cases hh
  | ovlFn _ ho => cases ht; rw [(c₀.isOvl_parts ho).2.1] at hh; cases hh
  | _ => cases ht

/-- An injection under `R`. -/
theorem EvalTermR.inj_inv_ksc {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm}
    (h : EvalTermR c₀ R σ (.inj a b t) r) : ∃ q, EvalTermR c₀ R σ t q ∧ r = q.map (injNormal a b) := by
  generalize ht : Term.inj a b t = u at h
  cases h with
  | inj h => cases ht; exact ⟨_, h, rfl⟩
  | _ => cases ht

/-! ## `eval` at an instance -/

/-- `eval(D, inst(P, B))` under `R`: where `inst` has no value, none; else a call of `eval` at the
instance. -/
theorem instCall_inv_ksc (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {σ : Subst} {i j k : Nat}
    {E : D} {p : T} {B : Bind} {r : Option GroundTerm} (hi : σ.lookup i = some (embD E))
    (hj : σ.lookup j = some (emb p)) (hk : σ.lookup k = some (embB B))
    (h : EvalTermR c₀ R σ (.app 464 [.var i, .app 476 [.var j, .var k]]) r) :
    (instF p B = none ∧ r = none) ∨ ∃ t, instF p B = some t ∧ R 464 [embD E, emb t] r := by
  obtain ⟨q, hq, hcase⟩ := EvalTermR.callVarsT_ksc (ts := [.var i]) notCtor_464 notHook_464
    notParam_464 (by decide +kernel) (.cons hi .nil) h
  have h476 := EvalTermR.callVars_ksc notCtor_476 notHook_476 notParam_476 (by decide +kernel)
    (.cons hj (.cons hk .nil)) hq
  rw [(instF.eval_iff p B).mp (hR _ _ _ h476)] at hcase
  cases hp : instF p B with
  | none =>
    rw [hp] at hcase
    rcases hcase with ⟨_, hy, -⟩ | ⟨-, hr⟩
    · cases hy
    · exact .inl ⟨rfl, hr⟩
  | some t =>
    rw [hp] at hcase
    rcases hcase with ⟨_, hy, hR'⟩ | ⟨hn, -⟩
    · cases hy; exact .inr ⟨t, rfl, hR'⟩
    · cases hn

/-- `A =/=K B` on the K sequences of two terms whose values are embeddings. -/
theorem kneT_eval_ksc {σ : Subst} {a b : Term} {t u : T} (ha : EvalTerm c₀ σ a (some (emb t)))
    (hb : EvalTerm c₀ σ b (some (emb u))) :
    EvalTerm c₀ σ (.app 30 [.app 0 [.inj 33 1 a, .app 1 []], .app 0 [.inj 33 1 b, .app 1 []]])
      (some (bool (!decide (t = u)))) := by
  refine EvalTerm.hook (by decide +kernel) rfl (.cons (kqT_eval_khw ha) (.cons (kqT_eval_khw hb) .nil))
    (fun vs hvs => ?_) (fun hn => by cases hn)
  cases hvs
  rw [← kqV_cmp_kht]
  refine Semantics.hookRes_of_value ((hook_kNe _ _).trans ?_)
  cases GroundTerm.cmp (kqV t) (kqV u) <;> rfl

/-- `eval(D, inst(P, B))` forward, at an instance `eval` gives the value `emb u`. -/
theorem instCall_eval_ksc {σ : Subst} {i j k : Nat} {E : D} {p t u : T} {B : Bind}
    (hi : σ.lookup i = some (embD E)) (hj : σ.lookup j = some (emb p))
    (hk : σ.lookup k = some (embB B)) (ht : instF p B = some t)
    (he : Eval c₀ 464 [embD E, emb t] (some (emb u))) :
    EvalTerm c₀ σ (.app 464 [.var i, .app 476 [.var j, .var k]]) (some (emb u)) := by
  have h476 : Eval c₀ 476 [emb p, embB B] (some (emb t)) := by
    have := instF.eval p B
    rw [ht] at this
    exact this
  exact ev_call (.cons (ev_var hi) (.cons (ev_call (.cons (ev_var hj) (.cons (ev_var hk) .nil)) h476) .nil)) he

theorem bvTrue_eval_ksc {σ : Subst} :
    EvalTerm c₀ σ (.app 413 [.dv 2 (.bool true)]) (some (emb (.bv true))) :=
  ev_ctor (.cons .dv .nil)

/-- **The `requires` of `try-holds` and `fire-holds`** (`==K`) under `R`: at an instance of the
requires' form, a call of `eval`, and where `eval` gives `emb u`, the requires is `u = bv(true)`. -/
theorem reqEq_inv_ksc (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {σ : Subst} {i j k : Nat}
    {E : D} {p : T} {B : Bind} {r : Option GroundTerm} (hi : σ.lookup i = some (embD E))
    (hj : σ.lookup j = some (emb p)) (hk : σ.lookup k = some (embB B))
    (h : EvalTermR c₀ R σ (WalkV.reqT_ksc 29 i j k) r) {t : T} (ht : instF p B = some t) :
    ∃ q, R 464 [embD E, emb t] q ∧ ∀ u, q = some (emb u) → r = some (bool (decide (u = .bv true))) := by
  obtain ⟨rs, hts, -, -⟩ := EvalTermR.hook_inv_ksc (by decide +kernel) (by decide +kernel) h
  rcases hts with _ | ⟨a0, _ | ⟨-, _ | _⟩⟩
  obtain ⟨rs0, hts0, -⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) a0
  rcases hts0 with _ | ⟨b0, _ | ⟨-, _ | _⟩⟩
  obtain ⟨qx, hx, -⟩ := EvalTermR.inj_inv_ksc b0
  rcases instCall_inv_ksc hR hi hj hk hx with ⟨hn, -⟩ | ⟨t', ht', hR'⟩
  · rw [ht] at hn; cases hn
  · rw [ht] at ht'; cases ht'
    refine ⟨qx, hR', fun u hu => ?_⟩
    subst hu
    exact EvalTermR.helper_val_ksc hR h
      (keqT_eval_khw (instCall_eval_ksc hi hj hk ht (hR _ _ _ hR')) bvTrue_eval_ksc)

/-- The `requires` of `try-refuted` and `fire-refuted` (`=/=K`) under `R`. -/
theorem reqNe_inv_ksc (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {σ : Subst} {i j k : Nat}
    {E : D} {p : T} {B : Bind} {r : Option GroundTerm} (hi : σ.lookup i = some (embD E))
    (hj : σ.lookup j = some (emb p)) (hk : σ.lookup k = some (embB B))
    (h : EvalTermR c₀ R σ (WalkV.reqT_ksc 30 i j k) r) {t : T} (ht : instF p B = some t) :
    ∃ q, R 464 [embD E, emb t] q ∧ ∀ u, q = some (emb u) → r = some (bool (!decide (u = .bv true))) := by
  obtain ⟨rs, hts, -, -⟩ := EvalTermR.hook_inv_ksc (by decide +kernel) (by decide +kernel) h
  rcases hts with _ | ⟨a0, _ | ⟨-, _ | _⟩⟩
  obtain ⟨rs0, hts0, -⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) a0
  rcases hts0 with _ | ⟨b0, _ | ⟨-, _ | _⟩⟩
  obtain ⟨qx, hx, -⟩ := EvalTermR.inj_inv_ksc b0
  rcases instCall_inv_ksc hR hi hj hk hx with ⟨hn, -⟩ | ⟨t', ht', hR'⟩
  · rw [ht] at hn; cases hn
  · rw [ht] at ht'; cases ht'
    refine ⟨qx, hR', fun u hu => ?_⟩
    subst hu
    exact EvalTermR.helper_val_ksc hR h
      (kneT_eval_ksc (instCall_eval_ksc hi hj hk ht (hR _ _ _ hR')) bvTrue_eval_ksc)

/-! ## The inversions -/

theorem tryMPlain_ksc : ∀ cl ∈ WalkV.tryMDef_ksc.clauses, cl.ens = none ∧ cl.exs = [] := by
  intro cl hcl
  simp only [WalkV.tryMDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- **`tryM` inverted.** At `.Ms`, `none`. At `m(B, Ms)` and an instance `t` of the `requires`'
form under `B`: `try-refuted` (the call of `eval` at `t` gives no `bv(true)`, and the result is
`tryM` at `Ms`), `try-holds` (it gives `bv(true)`, and the result is `some` of `eval` at the right
side's instance, none where there is none), or neither applies (two calls of `eval` at `t`, one
giving `bv(true)` and one not). -/
theorem tryM_inv_ksc (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {E : D} {req rhs : T} {ms : Ms}
    {r : Option GroundTerm} (hb : ByClause c₀ R 514 [embD E, emb req, emb rhs, embMs ms] r) :
    (ms = [] ∧ r = some (embRes none)) ∨
    ∃ B ms', ms = B :: ms' ∧ ∀ t, instF req B = some t →
      (∃ q, R 464 [embD E, emb t] q ∧ (∀ u, q = some (emb u) → u ≠ .bv true) ∧
        R 514 [embD E, emb req, emb rhs, embMs ms'] r) ∨
      (∃ q, R 464 [embD E, emb t] q ∧ (∀ u, q = some (emb u) → u = .bv true) ∧
        ((instF rhs B = none ∧ r = none) ∨
          ∃ t' q', instF rhs B = some t' ∧ R 464 [embD E, emb t'] q' ∧
            r = q'.map fun y => .ctor 439 [y])) ∨
      (∃ q q', R 464 [embD E, emb t] q ∧ R 464 [embD E, emb t] q' ∧
        (∀ u, q = some (emb u) → u = .bv true) ∧ (∀ u, q' = some (emb u) → u ≠ .bv true)) := by
  have hcases := byClause_cases_ksc hb WalkV.tryMDef_lookup_ksc tryMPlain_ksc
  cases ms with
  | nil =>
    refine .inl ⟨rfl, ?_⟩
    rcases hcases with ⟨cl, hmem, σ, -, hmatch, -, hrhs⟩ | ⟨-, hfail⟩
    · simp only [WalkV.tryMDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        rcases hmatch with _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨h3, _ | _⟩⟩⟩⟩
      · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim
      · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim
      · obtain ⟨rs, hrs, rfl⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) hrhs
        cases hrs; rfl
    · obtain ⟨_, _, hq, -⟩ := FailsR.req_ksc (hfail _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) rfl
        (σ := enumFrom 0 [embD E, emb req, emb rhs])
        (ws_enum (.cons (embD_sorted_c₀ E) (.cons (emb_sorted_c₀ req) (.cons (emb_sorted_c₀ rhs) .nil))))
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_403 .nil) .nil))))
      cases hq
  | cons B ms' =>
    refine .inr ⟨B, ms', rfl, fun t ht => ?_⟩
    rcases hcases with ⟨cl, hmem, σ, -, hmatch, hreq, hrhs⟩ | ⟨-, hfail⟩
    · simp only [WalkV.tryMDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩⟩
      · obtain ⟨xs, he, hxs⟩ := pv_ctor h3
        cases he
        rcases hxs with _ | ⟨hB, _ | ⟨hms, _ | _⟩⟩
        have h0 := PatVal.var_inv h0
        have h1 := PatVal.var_inv h1
        have h2 := PatVal.var_inv h2
        have hB := PatVal.var_inv hB
        have hms := PatVal.var_inv hms
        obtain ⟨q, hq, hv⟩ := reqNe_inv_ksc hR h0 h1 hB (hreq _ rfl) ht
        refine .inl ⟨q, hq, fun u hu he => ?_, EvalTermR.callVars_ksc notCtor_514 notHook_514
          notParam_514 (by decide +kernel) (.cons h0 (.cons h1 (.cons h2 (.cons hms .nil)))) hrhs⟩
        have := hv u hu
        subst he
        simp [bool] at this
      · obtain ⟨xs, he, hxs⟩ := pv_ctor h3
        cases he
        rcases hxs with _ | ⟨hB, _ | ⟨hms, _ | _⟩⟩
        have h0 := PatVal.var_inv h0
        have h1 := PatVal.var_inv h1
        have h2 := PatVal.var_inv h2
        have hB := PatVal.var_inv hB
        obtain ⟨q, hq, hv⟩ := reqEq_inv_ksc hR h0 h1 hB (hreq _ rfl) ht
        refine .inr (.inl ⟨q, hq, fun u hu => ?_, ?_⟩)
        · have := hv u hu
          by_cases hne : u = .bv true
          · exact hne
          · simp [hne, bool] at this
        · obtain ⟨rs, hrs, rfl⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) hrhs
          rcases hrs with _ | ⟨e0, _ | _⟩
          rcases instCall_inv_ksc hR h0 h2 hB e0 with ⟨hn, rfl⟩ | ⟨t', ht', hR'⟩
          · exact .inl ⟨hn, rfl⟩
          · refine .inr ⟨t', _, ht', hR', ?_⟩
            rename_i q'
            cases q' <;> rfl
      · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim
    · have hσ₀ := ws_enum (vars := [45, 33, 33, 46, 37]) (.cons (embD_sorted_c₀ E)
        (.cons (emb_sorted_c₀ req) (.cons (emb_sorted_c₀ rhs) (.cons (embB_sorted_c₀ B)
          (.cons (embMs_sorted_c₀ ms') .nil)))))
      have hp₀ : PatVals c₀ (enumFrom 0 [embD E, emb req, emb rhs, embB B, embMs ms'])
          [.var 0, .var 1, .var 2, .app 428 [.var 3, .var 4]] [embD E, emb req, emb rhs, embMs (B :: ms')] :=
        .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
          (.cons (.ctor ctor_428 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil)))
      obtain ⟨t1, r1, he1, hr1, hne1⟩ := FailsR.req_ksc (hfail _ (List.mem_cons_self ..)) rfl hσ₀ hp₀
      obtain ⟨t2, r2, he2, hr2, hne2⟩ := FailsR.req_ksc
        (hfail _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl hσ₀ hp₀
      cases he1
      cases he2
      obtain ⟨q, hq, hv⟩ := reqNe_inv_ksc hR rfl rfl rfl hr1 ht
      obtain ⟨q', hq', hv'⟩ := reqEq_inv_ksc hR rfl rfl rfl hr2 ht
      refine .inr (.inr ⟨q, q', hq, hq', fun u hu => ?_, fun u hu he => ?_⟩)
      · rw [hv u hu] at hne1
        by_cases hne : u = .bv true
        · exact hne
        · exact (hne1 (by simp [hne])).elim
      · rw [hv' u hu] at hne2
        exact hne2 (by simp [he])

/-! ### The functions without a `requires` -/

set_option hygiene false in
/-- The clauses of a function have no `requires`, ensures, existential variable or predicate. -/
macro "ksc_plain" dn:ident : tactic => `(tactic| (
  intro cl hcl
  simp only [$dn:ident, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩))

theorem resultPlain_ksc : ∀ cl ∈ WalkV.resultDef_ksc.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by ksc_plain WalkV.resultDef_ksc
theorem orElsePlain_ksc : ∀ cl ∈ WalkV.orElseDef_ksc.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by ksc_plain WalkV.orElseDef_ksc
theorem evalIfPlain_ksc : ∀ cl ∈ WalkV.evalIfDef_ksc.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by ksc_plain WalkV.evalIfDef_ksc
theorem evalAtPlain_ksc : ∀ cl ∈ WalkV.evalAtDef_ksc.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by ksc_plain WalkV.evalAtDef_ksc
theorem tryClPlain_ksc : ∀ cl ∈ WalkV.tryClDef_ksc.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by ksc_plain WalkV.tryClDef_ksc
theorem applyLPlain_ksc : ∀ cl ∈ EvalV.applyLDef_kev.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by ksc_plain EvalV.applyLDef_kev

/-- **`result` inverted**: the term `some` holds, `bot` at `none`. -/
theorem result_inv_ksc {f : Int} {ts : List T} {x : Option T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 502 [.dv 3 (.int f), embTs ts, embRes x] r) : r = some (emb (x.getD .bot)) := by
  cases x with
  | none =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkV.resultDef_lookup_ksc resultPlain_ksc
      (List.mem_cons_self ..) (σ₀ := enumFrom 0 [.dv 3 (.int f), embTs ts])
      (ws_enum (.cons (sort_int f) (.cons (embTs_sorted_c₀ ts) .nil)))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_433 .nil) .nil)))
    simp only [WalkV.resultDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨-, _ | ⟨-, _ | ⟨h2, _ | _⟩⟩⟩
    · obtain ⟨rs, hrs, rfl⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) hrhs
      cases hrs; rfl
    · exact (patCtor_ne_kht h2 (fun ws h => by cases h)).elim
  | some t =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkV.resultDef_lookup_ksc resultPlain_ksc
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (σ₀ := enumFrom 0 [.dv 3 (.int f), embTs ts, emb t])
      (ws_enum (.cons (sort_int f) (.cons (embTs_sorted_c₀ ts) (.cons (emb_sorted_c₀ t) .nil))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_439 (.cons (.var rfl) .nil)) .nil)))
    simp only [WalkV.resultDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨-, _ | ⟨-, _ | ⟨h2, _ | _⟩⟩⟩
    · exact (patCtor_ne_kht h2 (fun ws h => by cases h)).elim
    · obtain ⟨xs, he, hxs⟩ := pv_ctor h2
      cases he
      rcases hxs with _ | ⟨ht, _ | _⟩
      rw [EvalTermR.var_inv_kst hrhs, PatVal.var_inv ht]
      rfl

/-- **`orElse` inverted**: `some` stays; at `none`, `tryAt` at the rest of the clauses. -/
theorem orElse_inv_ksc {x : Option T} {E : D} {ts : List T} {cs : List Cl} {P : Int}
    {r : Option GroundTerm}
    (hb : ByClause c₀ R 497 [embRes x, embD E, embTs ts, embCls cs, .dv 3 (.int P)] r) :
    (∃ t, x = some t ∧ r = some (embRes x)) ∨
      (x = none ∧ R 512 [embD E, embTs ts, embCls cs, .dv 3 (.int P)] r) := by
  cases x with
  | some t =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkV.orElseDef_lookup_ksc orElsePlain_ksc
      (List.mem_cons_self ..)
      (σ₀ := enumFrom 0 [emb t, embRes (some t), embD E, embTs ts, embCls cs, .dv 3 (.int P)])
      (ws_enum (.cons (emb_sorted_c₀ t) (.cons (embRes_sorted_c₀ _) (.cons (embD_sorted_c₀ E)
        (.cons (embTs_sorted_c₀ ts) (.cons (embCls_sorted_c₀ cs) (.cons (sort_int P) .nil)))))))
      (.cons (.as (.ctor ctor_439 (.cons (.var rfl) .nil)) rfl)
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))))
    simp only [WalkV.orElseDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨h0, _⟩
    · refine .inl ⟨t, rfl, ?_⟩
      rw [EvalTermR.var_inv_kst hrhs, (PatVal.as_inv h0).2]
    · exact (patCtor_ne_kht h0 (fun ws h => by cases h)).elim
  | none =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkV.orElseDef_lookup_ksc orElsePlain_ksc
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (σ₀ := enumFrom 0 [embD E, embTs ts, embCls cs, .dv 3 (.int P)])
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embTs_sorted_c₀ ts) (.cons (embCls_sorted_c₀ cs)
        (.cons (sort_int P) .nil)))))
      (.cons (.ctor ctor_433 .nil) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))))
    simp only [WalkV.orElseDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | _⟩⟩⟩⟩⟩
    · exact (patCtor_ne_kht (PatVal.as_inv h0).1 (fun ws h => by cases h)).elim
    · exact .inr ⟨rfl, EvalTermR.callVars_ksc notCtor_512 notHook_512 notParam_512 (by decide +kernel)
        (.cons (PatVal.var_inv h1) (.cons (PatVal.var_inv h2) (.cons (PatVal.var_inv h3)
          (.cons (PatVal.var_inv h4) .nil)))) hrhs⟩

/-- **`evalIf` inverted**: `some` stays; at `none`, `evalAt` at the next priority. -/
theorem evalIf_inv_ksc (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {E : D} {ts : List T}
    {cs : List Cl} {P : Int} {x : Option T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 466 [embD E, embTs ts, embCls cs, .dv 3 (.int P), embRes x] r) :
    (∃ t, x = some t ∧ r = some (embRes x)) ∨
      (x = none ∧ R 465 [embD E, embTs ts, embCls cs, embPrio (nextClF cs (some P))] r) := by
  cases x with
  | some t =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkV.evalIfDef_lookup_ksc evalIfPlain_ksc
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (σ₀ := enumFrom 0 [embD E, embTs ts, embCls cs, .dv 3 (.int P), emb t, embRes (some t)])
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embTs_sorted_c₀ ts) (.cons (embCls_sorted_c₀ cs)
        (.cons (sort_int P) (.cons (emb_sorted_c₀ t) (.cons (embRes_sorted_c₀ _) .nil)))))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
        (.cons (.as (.ctor ctor_439 (.cons (.var rfl) .nil)) rfl) .nil)))))
    simp only [WalkV.evalIfDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨h4, _ | _⟩⟩⟩⟩⟩
    · exact (patCtor_ne_kht h4 (fun ws h => by cases h)).elim
    · refine .inl ⟨t, rfl, ?_⟩
      rw [EvalTermR.var_inv_kst hrhs, (PatVal.as_inv h4).2]
  | none =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkV.evalIfDef_lookup_ksc evalIfPlain_ksc
      (List.mem_cons_self ..)
      (σ₀ := enumFrom 0 [embD E, embTs ts, embCls cs, .dv 3 (.int P)])
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embTs_sorted_c₀ ts) (.cons (embCls_sorted_c₀ cs)
        (.cons (sort_int P) .nil)))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
        (.cons (.ctor ctor_433 .nil) .nil)))))
    simp only [WalkV.evalIfDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | _⟩⟩⟩⟩⟩
    · have h0 := PatVal.var_inv h0
      have h1 := PatVal.var_inv h1
      have h2 := PatVal.var_inv h2
      have h3 := PatVal.var_inv h3
      obtain ⟨q, hq, hcase⟩ := EvalTermR.callVarsT_ksc (ts := [.var 0, .var 1, .var 2]) notCtor_465
        notHook_465 notParam_465 (by decide +kernel) (.cons h0 (.cons h1 (.cons h2 .nil))) hrhs
      have hv := EvalTermR.helper_val_ksc hR hq
        (ev_call (.cons (ev_var h2) (.cons (ev_ctor (.cons (ev_var h3) .nil)) .nil)) (nextClF.eval cs (some P)))
      subst hv
      rcases hcase with ⟨y, hy, hR'⟩ | ⟨hn, -⟩
      · cases hy; exact .inr ⟨rfl, hR'⟩
      · cases hn
    · exact (patCtor_ne_kht (PatVal.as_inv h4).1 (fun ws h => by cases h)).elim

/-- **`evalAt` inverted**: at `noP`, `none`; at `at(P)`, `tryAt` at `P`, then `evalIf`. -/
theorem evalAt_inv_ksc {E : D} {ts : List T} {cs : List Cl} {p : Option Int} {r : Option GroundTerm}
    (hb : ByClause c₀ R 465 [embD E, embTs ts, embCls cs, embPrio p] r) :
    (p = none ∧ r = some (embRes none)) ∨
      ∃ P, p = some P ∧ ∃ q, R 512 [embD E, embTs ts, embCls cs, .dv 3 (.int P)] q ∧
        ((∃ y, q = some y ∧ R 466 [embD E, embTs ts, embCls cs, .dv 3 (.int P), y] r) ∨
          (q = none ∧ r = none)) := by
  cases p with
  | none =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkV.evalAtDef_lookup_ksc evalAtPlain_ksc
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (σ₀ := enumFrom 0 [embD E, embTs ts, embCls cs])
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embTs_sorted_c₀ ts) (.cons (embCls_sorted_c₀ cs) .nil))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_431 .nil) .nil))))
    simp only [WalkV.evalAtDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨h3, _ | _⟩⟩⟩⟩
    · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim
    · obtain ⟨rs, hrs, rfl⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) hrhs
      cases hrs
      exact .inl ⟨rfl, rfl⟩
  | some P =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkV.evalAtDef_lookup_ksc evalAtPlain_ksc
      (List.mem_cons_self ..)
      (σ₀ := enumFrom 0 [embD E, embTs ts, embCls cs, .dv 3 (.int P)])
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embTs_sorted_c₀ ts) (.cons (embCls_sorted_c₀ cs)
        (.cons (sort_int P) .nil)))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_410 (.cons (.var rfl) .nil)) .nil))))
    simp only [WalkV.evalAtDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩⟩
    · obtain ⟨xs, he, hxs⟩ := pv_ctor h3
      cases he
      rcases hxs with _ | ⟨h3, _ | _⟩
      have hv : VarsAre_ksc σ [.var 0, .var 1, .var 2, .var 3]
          [embD E, embTs ts, embCls cs, .dv 3 (.int P)] :=
        .cons (PatVal.var_inv h0) (.cons (PatVal.var_inv h1) (.cons (PatVal.var_inv h2)
          (.cons (PatVal.var_inv h3) .nil)))
      obtain ⟨q, hq, hcase⟩ := EvalTermR.callVarsT_ksc notCtor_466 notHook_466 notParam_466
        (by decide +kernel) hv hrhs
      exact .inr ⟨P, rfl, q, EvalTermR.callVars_ksc notCtor_512 notHook_512 notParam_512
        (by decide +kernel) hv hq, hcase⟩
    · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim

/-- **`tryCl` inverted**: `tryM` at what `matchTs` gives the clause's patterns, none where it
gives none. -/
theorem tryCl_inv_ksc (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {E : D} {ps : List T}
    {req rhs : T} {as : List T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 513 [embD E, embTs ps, emb req, emb rhs, embTs as] r) :
    (∃ M, matchTsF E.subs ps as [] = some M ∧ R 514 [embD E, emb req, emb rhs, embMs M] r) ∨
      (matchTsF E.subs ps as [] = none ∧ r = none) := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkV.tryClDef_lookup_ksc tryClPlain_ksc
    (List.mem_cons_self ..)
    (σ₀ := enumFrom 0 [embD E, embTs ps, emb req, emb rhs, embTs as])
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embTs_sorted_c₀ ps) (.cons (emb_sorted_c₀ req)
      (.cons (emb_sorted_c₀ rhs) (.cons (embTs_sorted_c₀ as) .nil))))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))))
  simp only [WalkV.tryClDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | _⟩⟩⟩⟩⟩
  have h0 := PatVal.var_inv h0
  have h1 := PatVal.var_inv h1
  have h2 := PatVal.var_inv h2
  have h3 := PatVal.var_inv h3
  have h4 := PatVal.var_inv h4
  obtain ⟨q, hq, hcase⟩ := EvalTermR.callVarsT_ksc (ts := [.var 0, .var 2, .var 3]) notCtor_514
    notHook_514 notParam_514 (by decide +kernel) (.cons h0 (.cons h2 (.cons h3 .nil))) hrhs
  have hsubs : EvalTerm c₀ σ (.app 509 [.var 0]) (some (embS E.subs)) :=
    ev_call (.cons (ev_var h0) .nil) (Gen.subsOfF.eval E)
  have hv := EvalTermR.helper_val_ksc hR hq
    (ev_call (.cons (ev_var h1) (.cons (ev_var h4) (.cons (ev_ctor .nil (f := 400)) (.cons hsubs .nil))))
      (matchTs_eval_col E.subs ps as []))
  subst hv
  cases hM : matchTsF E.subs ps as [] with
  | none =>
    rw [hM] at hcase
    rcases hcase with ⟨_, hy, -⟩ | ⟨-, hr⟩
    · cases hy
    · exact .inr ⟨rfl, hr⟩
  | some M =>
    rw [hM] at hcase
    rcases hcase with ⟨_, hy, hR'⟩ | ⟨hn, -⟩
    · cases hy; exact .inl ⟨M, rfl, hR'⟩
    · cases hn

/-! ### The functions with a `requires` -/

theorem tryAtPlain_ksc : ∀ cl ∈ WalkV.tryAtDef_ksc.clauses, cl.ens = none ∧ cl.exs = [] := by
  intro cl hcl
  simp only [WalkV.tryAtDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- `cprio(Q, O) ==Int P` and `=/=Int`, forward. -/
theorem cprioCmp_eval_ksc {σ : Subst} {p : Int} {o : Bool} {P : Int}
    (h2 : σ.lookup 2 = some (.dv 3 (.int p))) (h3 : σ.lookup 3 = some (.dv 2 (.bool o)))
    (h8 : σ.lookup 8 = some (.dv 3 (.int P))) :
    EvalTerm c₀ σ (.app 23 [.app 460 [.var 2, .var 3], .var 8]) (some (bool (decide (cprioF p o = P)))) ∧
    EvalTerm c₀ σ (.app 24 [.app 460 [.var 2, .var 3], .var 8]) (some (bool (decide (cprioF p o ≠ P)))) :=
  have hc := ev_call (σ := σ) (.cons (ev_var h2) (.cons (ev_var h3) .nil)) (cprioF.eval p o)
  ⟨ev_int2 (P := (· = ·)) hook_intEq hc (ev_var h8), ev_int2 (P := (· ≠ ·)) hook_intNe hc (ev_var h8)⟩

/-- **`tryAt` inverted**: at `.Cls`, `none`; at a clause of priority `P`, `tryCl` at it, then
`orElse` at the rest; at a clause of another priority, `tryAt` at the rest. -/
theorem tryAt_inv_ksc (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {E : D} {ts : List T}
    {cs : List Cl} {P : Int} {r : Option GroundTerm}
    (hb : ByClause c₀ R 512 [embD E, embTs ts, embCls cs, .dv 3 (.int P)] r) :
    (cs = [] ∧ r = some (embRes none)) ∨
      ∃ c cs', cs = c :: cs' ∧
        ((cprioF c.prio c.owise = P ∧
          ∃ q, R 513 [embD E, embTs c.pats, emb c.req, emb c.rhs, embTs ts] q ∧
            ((∃ y, q = some y ∧ R 497 [y, embD E, embTs ts, embCls cs', .dv 3 (.int P)] r) ∨
              (q = none ∧ r = none))) ∨
         (cprioF c.prio c.owise ≠ P ∧ R 512 [embD E, embTs ts, embCls cs', .dv 3 (.int P)] r)) := by
  have hcases := byClause_cases_ksc hb WalkV.tryAtDef_lookup_ksc tryAtPlain_ksc
  cases cs with
  | nil =>
    refine .inl ⟨rfl, ?_⟩
    rcases hcases with ⟨cl, hmem, σ, -, hmatch, -, hrhs⟩ | ⟨-, hfail⟩
    · simp only [WalkV.tryAtDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        rcases hmatch with _ | ⟨-, _ | ⟨-, _ | ⟨h2, _ | ⟨-, _ | _⟩⟩⟩⟩
      · exact (patCtor_ne_kht h2 (fun ws h => by cases h)).elim
      · exact (patCtor_ne_kht h2 (fun ws h => by cases h)).elim
      · obtain ⟨rs, hrs, rfl⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) hrhs
        cases hrs; rfl
    · obtain ⟨_, _, hq, -⟩ := FailsR.req_ksc (hfail _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) rfl
        (σ := enumFrom 0 [embD E, embTs ts, .dv 3 (.int P)])
        (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embTs_sorted_c₀ ts) (.cons (sort_int P) .nil))))
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_401 .nil) (.cons (.var rfl) .nil))))
      cases hq
  | cons c cs' =>
    refine .inr ⟨c, cs', rfl, ?_⟩
    rcases hcases with ⟨cl, hmem, σ, -, hmatch, hreq, hrhs⟩ | ⟨-, hfail⟩
    · simp only [WalkV.tryAtDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h8, _ | _⟩⟩⟩⟩
      · obtain ⟨xs, he, hxs⟩ := pv_ctor h2
        cases he
        rcases hxs with _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, _ | ⟨g5, _ | ⟨g6, _ | ⟨g7, _ | _⟩⟩⟩⟩⟩⟩
        have h0 := PatVal.var_inv h0
        have h1 := PatVal.var_inv h1
        have h8 := PatVal.var_inv h8
        have hq := EvalTermR.helper_val_ksc hR (hreq _ rfl)
          (cprioCmp_eval_ksc (PatVal.var_inv g2) (PatVal.var_inv g3) h8).1
        have hP : cprioF c.prio c.owise = P := by simpa [bool] using hq
        obtain ⟨q, hq, hcase⟩ := EvalTermR.callTVars_ksc notCtor_497 notHook_497 notParam_497
          (by decide +kernel) (.cons h0 (.cons h1 (.cons (PatVal.var_inv g7) (.cons h8 .nil)))) hrhs
        exact .inl ⟨hP, q, EvalTermR.callVars_ksc notCtor_513 notHook_513 notParam_513 (by decide +kernel)
          (.cons h0 (.cons (PatVal.var_inv g4) (.cons (PatVal.var_inv g5) (.cons (PatVal.var_inv g6)
            (.cons h1 .nil))))) hq, hcase⟩
      · obtain ⟨xs, he, hxs⟩ := pv_ctor h2
        cases he
        rcases hxs with _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, _ | ⟨g5, _ | ⟨g6, _ | ⟨g7, _ | _⟩⟩⟩⟩⟩⟩
        have h0 := PatVal.var_inv h0
        have h1 := PatVal.var_inv h1
        have h8 := PatVal.var_inv h8
        have hq := EvalTermR.helper_val_ksc hR (hreq _ rfl)
          (cprioCmp_eval_ksc (PatVal.var_inv g2) (PatVal.var_inv g3) h8).2
        have hP : cprioF c.prio c.owise ≠ P := by simpa [bool] using hq
        exact .inr ⟨hP, EvalTermR.callVars_ksc notCtor_512 notHook_512 notParam_512 (by decide +kernel)
          (.cons h0 (.cons h1 (.cons (PatVal.var_inv g7) (.cons h8 .nil)))) hrhs⟩
      · exact (patCtor_ne_kht h2 (fun ws h => by cases h)).elim
    · have hσ₀ := ws_enum (vars := [45, 43, 3, 2, 43, 33, 33, 35, 3]) (.cons (embD_sorted_c₀ E)
        (.cons (embTs_sorted_c₀ ts) (.cons (sort_int c.prio) (.cons (sort_bool c.owise)
          (.cons (embTs_sorted_c₀ c.pats) (.cons (emb_sorted_c₀ c.req) (.cons (emb_sorted_c₀ c.rhs)
            (.cons (embCls_sorted_c₀ cs') (.cons (sort_int P) .nil)))))))))
      have hp₀ : PatVals c₀ (enumFrom 0 [embD E, embTs ts, .dv 3 (.int c.prio), .dv 2 (.bool c.owise),
            embTs c.pats, emb c.req, emb c.rhs, embCls cs', .dv 3 (.int P)])
          [.var 0, .var 1, .app 415 [.var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .var 8]
          [embD E, embTs ts, embCls (c :: cs'), .dv 3 (.int P)] :=
        .cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_415 (.cons (.var rfl) (.cons (.var rfl)
          (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))))) (.cons (.var rfl) .nil)))
      obtain ⟨t1, r1, he1, hr1, hne1⟩ := FailsR.req_ksc (hfail _ (List.mem_cons_self ..)) rfl hσ₀ hp₀
      obtain ⟨t2, r2, he2, hr2, hne2⟩ := FailsR.req_ksc
        (hfail _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl hσ₀ hp₀
      cases he1
      cases he2
      have hc := cprioCmp_eval_ksc (σ := enumFrom 0 [embD E, embTs ts, .dv 3 (.int c.prio),
        .dv 2 (.bool c.owise), embTs c.pats, emb c.req, emb c.rhs, embCls cs', .dv 3 (.int P)]) rfl rfl rfl
      rw [EvalTermR.helper_val_ksc hR hr1 hc.1] at hne1
      rw [EvalTermR.helper_val_ksc hR hr2 hc.2] at hne2
      by_cases h : cprioF c.prio c.owise = P
      · exact (hne1 (by simp [h])).elim
      · exact (hne2 (by simp [h])).elim

/-! ### `apply` and `applyL` -/

/-- kore.k's `lookup(F, Fs)` over the mirrors: the clauses of the first function numbered `F`. -/
def lookFnF_ksc (f : Int) : List (Int × List Cl) → Option (List Cl)
  | [] => none
  | (g, cs) :: fs => if f = g then some cs else lookFnF_ksc f fs

theorem lookupF_lookFn_ksc (f : Int) : ∀ fs : List (Int × List Cl),
    Gen.lookupF f fs = some (lookFnF_ksc f fs)
  | [] => rfl
  | (g, cs) :: fs => by
    unfold Gen.lookupF lookFnF_ksc
    by_cases h : f = g
    · simp [h]
    · simp [h, lookupF_lookFn_ksc f fs]

theorem applyPlain_ksc : ∀ cl ∈ EvalV.applyDef_kev.clauses, cl.ens = none ∧ cl.exs = [] := by
  intro cl hcl
  simp only [EvalV.applyDef_kev, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- **`apply` inverted**: `bot` where an argument is `bot`, else `applyL` at what `lookup` gives. -/
theorem apply_inv_ksc (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {E : D} {f : Int} {as : List T}
    {r : Option GroundTerm} (hb : ByClause c₀ R 448 [embD E, .dv 3 (.int f), embTs as] r) :
    (hasBotF as = true ∧ r = some (emb .bot)) ∨
      (hasBotF as = false ∧ R 449 [embD E, .dv 3 (.int f), embTs as, embLook (lookFnF_ksc f E.fns)] r) := by
  have hcases := byClause_cases_ksc hb EvalV.applyDef_lookup_kev applyPlain_ksc
  rcases hcases with ⟨cl, hmem, σ, -, hmatch, hreq, hrhs⟩ | ⟨-, hfail⟩
  · simp only [EvalV.applyDef_kev, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨h0, _ | ⟨h4, _ | ⟨h5, _ | _⟩⟩⟩
    · obtain ⟨hD, h3⟩ := PatVal.as_inv h0
      obtain ⟨xs, he, hxs⟩ := pv_ctor hD
      cases he
      rcases hxs with _ | ⟨-, _ | ⟨g1, _ | ⟨-, _ | _⟩⟩⟩
      have h4 := PatVal.var_inv h4
      have h5 := PatVal.var_inv h5
      have hq := EvalTermR.helper_val_ksc hR (hreq _ rfl)
        (not_eval_kev (ev_call (.cons (ev_var h5) .nil) (hasBotF.eval as)))
      have hbot : hasBotF as = false := by simpa [bool] using hq
      obtain ⟨q, hq, hcase⟩ := EvalTermR.callVarsT_ksc (ts := [.var 3, .var 4, .var 5]) notCtor_449
        notHook_449 notParam_449 (by decide +kernel) (.cons h3 (.cons h4 (.cons h5 .nil))) hrhs
      have hl : Eval c₀ 485 [.dv 3 (.int f), embFns E.fns] (some (embLook (lookFnF_ksc f E.fns))) := by
        have := Gen.lookupF.eval f E.fns
        rw [lookupF_lookFn_ksc] at this
        exact this
      have hv := EvalTermR.helper_val_ksc hR hq
        (ev_call (.cons (ev_var h4) (.cons (ev_var (PatVal.var_inv g1)) .nil)) hl)
      subst hv
      rcases hcase with ⟨y, hy, hR'⟩ | ⟨hn, -⟩
      · cases hy; exact .inr ⟨hbot, hR'⟩
      · cases hn
    · have hq := EvalTermR.helper_val_ksc hR (hreq _ rfl)
        (ev_call (.cons (ev_var (PatVal.var_inv h5)) .nil) (hasBotF.eval as))
      have hbot : hasBotF as = true := by simpa [bool] using hq
      obtain ⟨rs, hrs, rfl⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) hrhs
      cases hrs
      exact .inl ⟨hbot, rfl⟩
  · have hσ₀ := ws_enum (vars := [32, 39, 42, 45, 3, 43]) (.cons (embS_sorted_c₀ E.subs)
      (.cons (embFns_sorted_c₀ E.fns) (.cons (embRls_sorted_c₀ E.rules) (.cons (embD_sorted_c₀ E)
        (.cons (sort_int f) (.cons (embTs_sorted_c₀ as) .nil))))))
    have hp₀ : PatVals c₀ (enumFrom 0 [embS E.subs, embFns E.fns, embRls E.rules, embD E, .dv 3 (.int f), embTs as])
        [.as (.app 417 [.var 0, .var 1, .var 2]) 3, .var 4, .var 5] [embD E, .dv 3 (.int f), embTs as] :=
      .cons (.as (.ctor ctor_417 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) rfl)
        (.cons (.var rfl) (.cons (.var rfl) .nil))
    have hσ₁ := ws_enum (vars := [45, 3, 43]) (.cons (embD_sorted_c₀ E) (.cons (sort_int f)
      (.cons (embTs_sorted_c₀ as) .nil)))
    have hp₁ : PatVals c₀ (enumFrom 0 [embD E, .dv 3 (.int f), embTs as]) [.var 0, .var 1, .var 2]
        [embD E, .dv 3 (.int f), embTs as] :=
      .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))
    obtain ⟨t1, r1, he1, hr1, hne1⟩ := FailsR.req_ksc (hfail _ (List.mem_cons_self ..)) rfl hσ₀ hp₀
    obtain ⟨t2, r2, he2, hr2, hne2⟩ := FailsR.req_ksc
      (hfail _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl hσ₁ hp₁
    cases he1
    cases he2
    rw [EvalTermR.helper_val_ksc hR hr1 (not_eval_kev (ev_call (.cons (ev_var rfl) .nil) (hasBotF.eval as)))] at hne1
    rw [EvalTermR.helper_val_ksc hR hr2 (ev_call (.cons (ev_var rfl) .nil) (hasBotF.eval as))] at hne2
    cases h : hasBotF as
    · exact (hne1 (by rw [h]; rfl)).elim
    · exact (hne2 (by rw [h]; rfl)).elim

/-- **`applyL` inverted**: at `nofn`, the constructor application; at `fnd(Cs)`, `evalAt` from the
first priority, then `result`. -/
theorem applyL_inv_ksc (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {E : D} {f : Int} {as : List T}
    {l : Option (List Cl)} {r : Option GroundTerm}
    (hb : ByClause c₀ R 449 [embD E, .dv 3 (.int f), embTs as, embLook l] r) :
    (l = none ∧ r = some (emb (.ap f as))) ∨
      ∃ cs, l = some cs ∧ ∃ q, R 465 [embD E, embTs as, embCls cs, embPrio (nextClF cs none)] q ∧
        ((∃ y, q = some y ∧ R 502 [.dv 3 (.int f), embTs as, y] r) ∨ (q = none ∧ r = none)) := by
  cases l with
  | none =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb EvalV.applyLDef_lookup_kev applyLPlain_ksc
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (σ₀ := enumFrom 0 [embD E, .dv 3 (.int f), embTs as])
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (sort_int f) (.cons (embTs_sorted_c₀ as) .nil))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_432 .nil) .nil))))
    simp only [EvalV.applyLDef_kev, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨-, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩⟩
    · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim
    · obtain ⟨rs, hrs, rfl⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) hrhs
      rcases hrs with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩
      rw [EvalTermR.var_inv_kst e1, EvalTermR.var_inv_kst e2, PatVal.var_inv h1, PatVal.var_inv h2]
      exact .inl ⟨rfl, rfl⟩
  | some cs =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb EvalV.applyLDef_lookup_kev applyLPlain_ksc
      (List.mem_cons_self ..)
      (σ₀ := enumFrom 0 [embD E, .dv 3 (.int f), embTs as, embCls cs])
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (sort_int f) (.cons (embTs_sorted_c₀ as)
        (.cons (embCls_sorted_c₀ cs) .nil)))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_422 (.cons (.var rfl) .nil)) .nil))))
    simp only [EvalV.applyLDef_kev, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩⟩
    · obtain ⟨xs, he, hxs⟩ := pv_ctor h3
      cases he
      rcases hxs with _ | ⟨h3, _ | _⟩
      have h0 := PatVal.var_inv h0
      have h1 := PatVal.var_inv h1
      have h2 := PatVal.var_inv h2
      have h3 := PatVal.var_inv h3
      obtain ⟨q, hq, hcase⟩ := EvalTermR.callVarsT_ksc (ts := [.var 1, .var 2]) notCtor_502
        notHook_502 notParam_502 (by decide +kernel) (.cons h1 (.cons h2 .nil)) hrhs
      obtain ⟨q2, hq2, hcase2⟩ := EvalTermR.callVarsT_ksc (ts := [.var 0, .var 2, .var 3]) notCtor_465
        notHook_465 notParam_465 (by decide +kernel) (.cons h0 (.cons h2 (.cons h3 .nil))) hq
      have hv := EvalTermR.helper_val_ksc hR hq2
        (ev_call (.cons (ev_var h3) (.cons (ev_ctor .nil (f := 431)) .nil)) (nextClF.eval cs none))
      subst hv
      rcases hcase2 with ⟨y, hy, hR'⟩ | ⟨hn, -⟩
      · cases hy; exact .inr ⟨cs, rfl, q, hR', hcase⟩
      · cases hn
    · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim

/-! ## The priorities -/

/-- `q` is above the bound `b` (any `q` at `noP`). -/
def Above_ksc (q : Int) : Option Int → Prop
  | none => True
  | some b => b < q

instance Above_ksc.dec (q : Int) : (b : Option Int) → Decidable (Above_ksc q b)
  | none => isTrue trivial
  | some b => inferInstanceAs (Decidable (b < q))

theorem overF_ksc (p : Int) (b : Option Int) : overF p b = if Above_ksc p b then some p else none := by
  cases b with
  | none => simp [overF, Above_ksc]
  | some b => simp only [overF, Above_ksc]; by_cases h : p > b <;> simp [h]

/-- **The least of the priorities above a bound**, as `nextCl` and `nextRl` compute it: none where
no priority is above the bound, else a priority above it that no priority above it is below. -/
theorem leastOver_spec_ksc (b : Option Int) : ∀ ps : List Int,
    (ps.foldr (fun p acc => leastF (overF p b) acc) none = none → ∀ p ∈ ps, ¬ Above_ksc p b) ∧
    ∀ q, ps.foldr (fun p acc => leastF (overF p b) acc) none = some q →
      q ∈ ps ∧ Above_ksc q b ∧ ∀ p ∈ ps, Above_ksc p b → q ≤ p
  | [] => ⟨fun _ c hc => (nomatch hc), fun q h => (nomatch h)⟩
  | p :: ps => by
    obtain ⟨ih1, ih2⟩ := leastOver_spec_ksc b ps
    simp only [List.foldr_cons]
    rw [overF_ksc]
    by_cases ha : Above_ksc p b
    · rw [if_pos ha]
      cases hn : ps.foldr (fun p acc => leastF (overF p b) acc) none with
      | none =>
        refine ⟨fun h => (nomatch h), fun q hq => ?_⟩
        cases hq
        refine ⟨List.mem_cons_self .., ha, fun p' hp' ha' => ?_⟩
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact Int.le_refl _
        · exact absurd ha' (ih1 hn p' hp')
      | some q' =>
        obtain ⟨hm₁, ha₁, hmin⟩ := ih2 q' hn
        refine ⟨fun h => ?_, fun q hq => ?_⟩
        · simp only [leastF] at h; split at h <;> cases h
        · simp only [leastF] at hq
          by_cases hle : p ≤ q'
          · rw [if_pos hle] at hq; cases hq
            refine ⟨List.mem_cons_self .., ha, fun p' hp' ha' => ?_⟩
            rcases List.mem_cons.mp hp' with rfl | hp'
            · exact Int.le_refl _
            · exact Int.le_trans hle (hmin p' hp' ha')
          · rw [if_neg hle] at hq; cases hq
            refine ⟨List.mem_cons_of_mem _ hm₁, ha₁, fun p' hp' ha' => ?_⟩
            rcases List.mem_cons.mp hp' with rfl | hp'
            · exact Int.le_of_lt (Int.not_le.mp hle)
            · exact hmin p' hp' ha'
    · rw [if_neg ha]
      refine ⟨fun h p' hp' ha' => ?_, fun q hq => ?_⟩
      · rcases List.mem_cons.mp hp' with rfl | hp'
        · exact ha ha'
        · exact ih1 h p' hp' ha'
      · obtain ⟨hm₁, ha₁, hmin⟩ := ih2 q hq
        refine ⟨List.mem_cons_of_mem _ hm₁, ha₁, fun p' hp' ha' => ?_⟩
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact absurd ha' ha
        · exact hmin p' hp' ha'

/-- `nextCl` is the least of the clauses' priorities above the bound. -/
theorem nextClF_foldr_ksc (b : Option Int) : ∀ cs : List Cl,
    nextClF cs b = (cs.map fun c => cprioF c.prio c.owise).foldr (fun p acc => leastF (overF p b) acc) none
  | [] => rfl
  | c :: cs => by rw [List.map_cons, List.foldr_cons, ← nextClF_foldr_ksc b cs]; rfl

/-- `nextRl` is the least of the rules' priorities above the bound. -/
theorem nextRlF_foldr_ksc (b : Option Int) : ∀ rs : List Rl,
    nextRlF rs b = (rs.map fun r => rprioF r.prio r.owise).foldr (fun p acc => leastF (overF p b) acc) none
  | [] => rfl
  | r :: rs => by rw [List.map_cons, List.foldr_cons, ← nextRlF_foldr_ksc b rs]; rfl

/-- **`nextCl` gives the least priority above its bound**: none where no clause is above it. -/
theorem nextClF_spec_ksc (b : Option Int) (cs : List Cl) :
    (nextClF cs b = none → ∀ c ∈ cs, ¬ Above_ksc (cprioF c.prio c.owise) b) ∧
    ∀ q, nextClF cs b = some q → (∃ c ∈ cs, cprioF c.prio c.owise = q) ∧ Above_ksc q b ∧
      ∀ c ∈ cs, Above_ksc (cprioF c.prio c.owise) b → q ≤ cprioF c.prio c.owise := by
  rw [nextClF_foldr_ksc]
  obtain ⟨h1, h2⟩ := leastOver_spec_ksc b (cs.map fun c => cprioF c.prio c.owise)
  refine ⟨fun h c hc => h1 h _ (List.mem_map_of_mem hc), fun q hq => ?_⟩
  obtain ⟨hm, ha, hmin⟩ := h2 q hq
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
  exact ⟨⟨c, hc, rfl⟩, ha, fun c' hc' ha' => hmin _ (List.mem_map_of_mem hc') ha'⟩

/-- **`nextRl` gives the least priority above its bound**: none where no rule is above it. -/
theorem nextRlF_spec_ksc (b : Option Int) (rs : List Rl) :
    (nextRlF rs b = none → ∀ r ∈ rs, ¬ Above_ksc (rprioF r.prio r.owise) b) ∧
    ∀ q, nextRlF rs b = some q → (∃ r ∈ rs, rprioF r.prio r.owise = q) ∧ Above_ksc q b ∧
      ∀ r ∈ rs, Above_ksc (rprioF r.prio r.owise) b → q ≤ rprioF r.prio r.owise := by
  rw [nextRlF_foldr_ksc]
  obtain ⟨h1, h2⟩ := leastOver_spec_ksc b (rs.map fun r => rprioF r.prio r.owise)
  refine ⟨fun h r hr => h1 h _ (List.mem_map_of_mem hr), fun q hq => ?_⟩
  obtain ⟨hm, ha, hmin⟩ := h2 q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
  exact ⟨⟨r, hr, rfl⟩, ha, fun r' hr' ha' => hmin _ (List.mem_map_of_mem hr') ha'⟩

/-- An encoded clause's priority is its own. -/
theorem cprio_encCl_ksc (d : Semantics) (cl : Clause) :
    cprioF (encCl d cl).prio (encCl d cl).owise = (cl.prio : Int) := rfl

/-- **At the walk's first priority nothing is below.** -/
theorem below_first_ksc (d : Semantics) (fn : Fn) (ws : List GroundTerm) :
    Below_ksm d fn ws (nextClF (fn.clauses.map (encCl d)) none) := by
  intro cl hcl hlt
  have hm : encCl d cl ∈ fn.clauses.map (encCl d) := List.mem_map_of_mem hcl
  obtain ⟨h1, h2⟩ := nextClF_spec_ksc none (fn.clauses.map (encCl d))
  cases hq : nextClF (fn.clauses.map (encCl d)) none with
  | none => exact absurd trivial (h1 hq _ hm)
  | some q =>
    have hl := hlt q hq
    have := (h2 q hq).2.2 _ hm trivial
    rw [cprio_encCl_ksc] at this
    exact absurd hl (Int.not_lt.mpr this)

/-- **`ei-next`**: where every clause below `P` and every clause at `P` fails, every clause below
the next priority fails. -/
theorem below_next_ksc {d : Semantics} {fn : Fn} {ws : List GroundTerm} {P : Int}
    (hb : Below_ksm d fn ws (some P))
    (hP : ∀ cl ∈ fn.clauses, (cl.prio : Int) = P → Fails (d₀ d) ws cl) :
    Below_ksm d fn ws (nextClF (fn.clauses.map (encCl d)) (some P)) := by
  intro cl hcl hlt
  by_cases h1 : (cl.prio : Int) < P
  · exact hb cl hcl fun P' e => by cases e; exact h1
  by_cases h2 : (cl.prio : Int) = P
  · exact hP cl hcl h2
  have ha : Above_ksc (cprioF (encCl d cl).prio (encCl d cl).owise) (some P) := by
    show P < (cl.prio : Int); omega
  have hm : encCl d cl ∈ fn.clauses.map (encCl d) := List.mem_map_of_mem hcl
  obtain ⟨g1, g2⟩ := nextClF_spec_ksc (some P) (fn.clauses.map (encCl d))
  cases hq : nextClF (fn.clauses.map (encCl d)) (some P) with
  | none => exact absurd ha (g1 hq _ hm)
  | some q =>
    have hl := hlt q hq
    have := (g2 q hq).2.2 _ hm ha
    rw [cprio_encCl_ksc] at this
    exact absurd hl (Int.not_lt.mpr this)

end Inv

/-! ## Instances -/

section Instances
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms WalkV

/-- **`tryM` at a binding without the right side's variable has the result none**:
`tryM(D, bv(true), vr(0), m(.Bind, .Ms))`, where `try-holds` applies (its `requires` is true) and
its right side `some(eval(D, inst(vr(0), .Bind)))` has no value, `inst` having none. -/
theorem tryM_undef_ksc (E : D) :
    Eval (K₀ sig) 514 [embD E, emb (.bv true), emb (.vr 0), embMs [[]]] none := by
  have hσ := ws_enum (vars := [45, 33, 33, 46, 37]) (.cons (embD_sorted_c₀ E)
    (.cons (emb_sorted_c₀ (.bv true)) (.cons (emb_sorted_c₀ (.vr 0)) (.cons (embB_sorted_c₀ [])
      (.cons (embMs_sorted_c₀ []) .nil)))))
  have hp : PatVals c₀ (enumFrom 0 [embD E, emb (.bv true), emb (.vr 0), embB [], embMs []])
      [.var 0, .var 1, .var 2, .app 428 [.var 3, .var 4]]
      [embD E, emb (.bv true), emb (.vr 0), embMs [[]]] :=
    .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
      (.cons (.ctor ctor_428 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil)))
  have hbv : Eval c₀ 464 [embD E, emb (.bv true)] (some (emb (.bv true))) := eval_bv_kev E true
  refine clause_kht tryMDef_lookup_ksc (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hσ hp ?_
    (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
  · intro q hq
    cases hq
    have := keqT_eval_khw (instCall_eval_ksc (i := 0) (j := 1) (k := 3) (p := .bv true) (B := [])
      (σ := enumFrom 0 [embD E, emb (.bv true), emb (.vr 0), embB [], embMs []]) rfl rfl rfl rfl hbv)
      bvTrue_eval_ksc
    simpa using this
  · have h476 : Eval c₀ 476 [emb (.vr 0), embB []] none := instF.eval (.vr 0) []
    have hin : EvalTerm c₀ (enumFrom 0 [embD E, emb (.bv true), emb (.vr 0), embB [], embMs []])
        (.app 476 [.var 2, .var 3]) none := ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) h476
    have hev : EvalTerm c₀ (enumFrom 0 [embD E, emb (.bv true), emb (.vr 0), embB [], embMs []])
        (.app 464 [.var 0, .app 476 [.var 2, .var 3]]) none :=
      .callUndef notCtor_464 notHook_464 (.cons (ev_var rfl) (.cons hin .nil)) rfl notParam_464
    exact EvalTerm.ctor (rs := [none]) (by decide +kernel) (.cons hev .nil)

/-- **`result` at a code that is no Int has the result none**: no equation of `result` matches
`result(bv(true), .Ts, none)` (its first argument is a Bool), and no function of kore.k has a
rest. -/
theorem result_illSorted_ksc : Eval (K₀ sig) 502 [.dv 2 (.bool true), embTs [], embRes none] none := by
  refine Eval.rest (fn := resultDef_ksc) resultDef_lookup_ksc fun cl hcl => ?_
  simp only [resultDef_ksc, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl <;> refine .intro fun σ hw hm => ?_ <;> rcases hm with _ | ⟨h0, -⟩ <;>
    obtain ⟨w, hw0, hs⟩ := hw 0 (by decide) 3 rfl <;>
    rw [PatVal.var_inv h0] at hw0 <;> cases hw0 <;> rw [show (K₀ sig).sortOf _ = _ from sort_bool true] at hs <;> cases hs

/-- `tryM_inv_ksc` at `tryM_undef_ksc`'s evaluation: the binding `.Bind` has no instance of the
right side, and the result is none (the `try-holds` disjunct with `inst` undefined). -/
example (E : D) : ∃ B ms', [[]] = B :: ms' ∧ instF (.bv true) B = some (.bv true) ∧
    instF (.vr 0) B = none := by
  rcases tryM_inv_ksc (R := Eval c₀) (fun _ _ _ h => h)
    (Eval.byClause_iff.mp (tryM_undef_ksc E)) with ⟨h, -⟩ | ⟨B, ms', h, -⟩
  · cases h
  · cases h
    exact ⟨[], [], rfl, rfl, rfl⟩

/-- `result_inv_ksc` at an evaluation: `result(7, .Ts, some(iv(1)))` is `iv(1)`. -/
example (r : Option GroundTerm) (h : Eval c₀ 502 [.dv 3 (.int 7), embTs [], embRes (some (.iv 1))] r) :
    r = some (emb (.iv 1)) :=
  result_inv_ksc (R := Eval c₀) (Eval.byClause_iff.mp h)

/-- The walk's first priority at a clause list of priorities 50 and 200 is 50. -/
example : nextClF [⟨200, false, [], .bv true, .bot⟩, ⟨50, false, [], .bv true, .bot⟩] none = some 50 := rfl

end Instances

/-! ## Checks -/

open Lean in
#eval show CoreM Unit from do
  for n in [``WalkV.tryMDef_lookup_ksc, ``WalkV.tryClDef_lookup_ksc, ``WalkV.tryAtDef_lookup_ksc,
      ``WalkV.orElseDef_lookup_ksc, ``WalkV.resultDef_lookup_ksc, ``WalkV.evalAtDef_lookup_ksc,
      ``WalkV.evalIfDef_lookup_ksc, ``byClause_cases_ksc, ``FailsR.req_ksc,
      ``EvalTermR.helper_val_ksc, ``instCall_inv_ksc, ``reqEq_inv_ksc, ``reqNe_inv_ksc,
      ``tryM_inv_ksc, ``tryM_undef_ksc, ``result_illSorted_ksc, ``result_inv_ksc, ``orElse_inv_ksc, ``evalIf_inv_ksc,
      ``evalAt_inv_ksc, ``tryCl_inv_ksc, ``tryAt_inv_ksc, ``apply_inv_ksc, ``applyL_inv_ksc,
      ``lookupF_lookFn_ksc, ``leastOver_spec_ksc, ``nextClF_foldr_ksc, ``nextRlF_foldr_ksc,
      ``nextClF_spec_ksc, ``nextRlF_spec_ksc, ``below_first_ksc, ``below_next_ksc] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
