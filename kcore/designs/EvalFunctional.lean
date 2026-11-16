/-
  KCore. Evaluation has one result.

  `Eval` reads a function's clauses first match first, so two derivations at one argument list use
  the same clause: a clause before the one used fails, and a clause that applies does not fail. They
  may still use two matches of that clause (a pattern inside a list, a map entry at a key nothing
  fixes). `MatchIndependent` says the result does not depend on the match; it is all that
  functionality reads. No sorting hypothesis is needed.
-/
import KcoreSpec.EvalSound

set_option autoImplicit false

namespace KCore

open KCore.Exec

/-- The clause applies at `vs` under σ: σ is well sorted, the patterns denote `vs`, and the
`requires` evaluates to `true`. -/
def Clause.AppliesAt (c : Semantics) (cl : Clause) (σ : Subst) (vs : List GroundTerm) : Prop :=
  c.WellSorted cl.vars σ ∧ PatVals c σ cl.pats vs ∧
    ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))

/-- Two matches of the clause at one argument list give one result: they agree on the variables
of the right-hand side, or the right-hand side has the same result under both. The first
alternative is what a syntactic check shows without knowing that evaluation is functional; the
second is the semantic statement. -/
def MatchIndependent (c : Semantics) (cl : Clause) : Prop :=
  ∀ vs σ σ', cl.AppliesAt c σ vs → cl.AppliesAt c σ' vs →
    (∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∨
    ∀ r r', EvalTerm c σ cl.rhs r → EvalTerm c σ' cl.rhs r' → r = r'

/-- Every clause of every function is match independent. -/
def MatchIndependentAll (c : Semantics) : Prop :=
  ∀ f fn, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, MatchIndependent c cl

namespace EvalFunctional

variable {c : Semantics}

theorem split_cases {α : Type} {pre post pre' post' : List α} {a a' : α}
    (h : pre ++ a :: post = pre' ++ a' :: post') :
    a ∈ pre' ∨ a' ∈ pre ∨ (pre = pre' ∧ a = a' ∧ post = post') := by
  induction pre generalizing pre' with
  | nil =>
    cases pre' with
    | nil => simp only [List.nil_append, List.cons.injEq] at h; exact .inr (.inr ⟨rfl, h.1, h.2⟩)
    | cons b bs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact .inl (h.1 ▸ List.mem_cons_self ..)
  | cons b bs ih =>
    cases pre' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact .inr (.inl (h.1 ▸ List.mem_cons_self ..))
    | cons b' bs' =>
      simp only [List.cons_append, List.cons.injEq] at h
      rcases ih h.2 with h1 | h1 | ⟨h1, h2, h3⟩
      · exact .inl (List.mem_cons_of_mem _ h1)
      · exact .inr (.inl (List.mem_cons_of_mem _ h1))
      · exact .inr (.inr ⟨by rw [h.1, h1], h2, h3⟩)

abbrev M1 (c : Semantics) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ r', Eval c f vs r' → r = r'
abbrev M2 (c : Semantics) (vs : List GroundTerm) (cl : Clause) : Prop :=
  ∀ σ, cl.AppliesAt c σ vs → False
abbrev M3 (c : Semantics) (σ : Subst) (cl : Clause) : Prop :=
  (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → False
abbrev M4 (c : Semantics) (σ : Subst) (t : Term) (r : Option GroundTerm) : Prop :=
  ∀ r', EvalTerm c σ t r' → r = r'
abbrev M5 (c : Semantics) (σ : Subst) (ts : List Term) (rs : List (Option GroundTerm)) : Prop :=
  ∀ rs', EvalTerms c σ ts rs' → rs = rs'

/-- A clause that applies under σ, its `requires` having one result there, does not fail. -/
theorem not_fails {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true))) (hf : Fails c vs cl) : False := by
  cases hf with
  | intro h =>
    cases h σ hσ hmatch with
    | intro ht he hr => exact hr (ihreq _ ht _ he).symm

theorem case_clause (hmi : MatchIndependentAll c) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    {pre post : List Clause} {cl : Clause} {σ : Subst} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hcls : fn.clauses = pre ++ cl :: post)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hrhs : EvalTerm c σ cl.rhs r) (ihpre : ∀ cl' ∈ pre, M2 c vs cl')
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (ihrhs : M4 c σ cl.rhs r) : M1 c f vs r := by
  intro r' h'
  have hmem : cl ∈ fn.clauses := by rw [hcls]; simp
  cases h' with
  | clause hfn' hcls' hpre' hσ' hmatch' hreq' hrhs' =>
    rw [hfn] at hfn'; cases hfn'
    rcases split_cases (hcls.symm.trans hcls') with h1 | h1 | ⟨rfl, rfl, rfl⟩
    · exact (not_fails hσ hmatch ihreq (hpre' _ h1)).elim
    · exact (ihpre _ h1 _ ⟨hσ', hmatch', hreq'⟩).elim
    · rcases hmi f fn hfn cl hmem vs _ _ ⟨hσ, hmatch, hreq⟩ ⟨hσ', hmatch', hreq'⟩ with hv | hr
      · exact ihrhs r' (EvalTerm.congr hrhs' fun i hi => (hv i hi).symm)
      · exact hr _ _ hrhs hrhs'
  | owise hfn' hnone' _ _ =>
    rw [hfn] at hfn'; cases hfn'
    exact (not_fails hσ hmatch ihreq (hnone' _ hmem)).elim
  | undef hfn' hnone' _ =>
    rw [hfn] at hfn'; cases hfn'
    exact (not_fails hσ hmatch ihreq (hnone' _ hmem)).elim

theorem case_owise {f : Sym} {fn : Fn} {vs : List GroundTerm} {o : Owise} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (ho : fn.owise = some o)
    (ihnone : ∀ cl ∈ fn.clauses, M2 c vs cl) (ihrhs : M4 c (argSubst 0 vs) o.rhs r) :
    M1 c f vs r := by
  intro r' h'
  cases h' with
  | clause hfn' hcls' _ hσ' hmatch' hreq' _ =>
    rw [hfn] at hfn'; cases hfn'
    exact (ihnone _ (by rw [hcls']; simp) _ ⟨hσ', hmatch', hreq'⟩).elim
  | owise hfn' _ ho' hrhs' =>
    rw [hfn] at hfn'; cases hfn'
    rw [ho] at ho'; cases ho'
    exact ihrhs _ hrhs'
  | undef hfn' _ ho' =>
    rw [hfn] at hfn'; cases hfn'
    rw [ho] at ho'; cases ho'

theorem case_undef {f : Sym} {fn : Fn} {vs : List GroundTerm}
    (hfn : c.lookupFn f = some fn) (ho : fn.owise = none)
    (ihnone : ∀ cl ∈ fn.clauses, M2 c vs cl) : M1 c f vs none := by
  intro r' h'
  cases h' with
  | clause hfn' hcls' _ hσ' hmatch' hreq' _ =>
    rw [hfn] at hfn'; cases hfn'
    exact (ihnone _ (by rw [hcls']; simp) _ ⟨hσ', hmatch', hreq'⟩).elim
  | owise hfn' _ ho' _ =>
    rw [hfn] at hfn'; cases hfn'
    rw [ho] at ho'; cases ho'
  | undef => rfl

theorem case_inj {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm} (ih : M4 c σ t r) :
    M4 c σ (.inj a b t) (r.map (injNormal a b)) := by
  intro r' h'
  cases h' with
  | inj h'' => rw [ih _ h'']

theorem case_ctor {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = true) (ihts : M5 c σ ts rs) :
    M4 c σ (.app f ts) ((allSome rs).map (.ctor f)) := by
  intro r' h'
  cases h' with
  | ctor _ hts' => rw [ihts _ hts']
  | hook h => rw [hk] at h; cases h
  | param h => rw [hk] at h; cases h
  | call h => rw [hk] at h; cases h
  | callUndef h => rw [hk] at h; cases h

theorem case_hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = true)
    (hh : ∀ vs, allSome rs = some vs → hook f vs = some r) (hund : allSome rs = none → r = none)
    (ihts : M5 c σ ts rs) : M4 c σ (.app f ts) r := by
  intro r' h'
  cases h' with
  | ctor h => rw [hk] at h; cases h
  | hook _ _ hts' hh' hund' =>
    have := ihts _ hts'; subst this
    cases hall : allSome rs with
    | none => rw [hund hall, hund' hall]
    | some vs => exact Option.some.inj ((hh vs hall).symm.trans (hh' vs hall))
  | param _ h => rw [hhk] at h; cases h
  | call _ h => rw [hhk] at h; cases h
  | callUndef _ h => rw [hhk] at h; cases h

theorem case_param {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = false)
    (hp : c.isParam f = true) (hr : r = (allSome rs).bind (c.paramVal f))
    (ihts : M5 c σ ts rs) : M4 c σ (.app f ts) r := by
  intro r' h'
  cases h' with
  | ctor h => rw [hk] at h; cases h
  | hook _ h => rw [hhk] at h; cases h
  | param _ _ _ hts' hr' => have := ihts _ hts'; subst this; rw [hr, hr']
  | call _ _ _ _ _ h => rw [hp] at h; cases h
  | callUndef _ _ _ _ h => rw [hp] at h; cases h

theorem case_call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {vs : List GroundTerm} {r : Option GroundTerm} (hk : c.isCtor f = false)
    (hhk : isHook f = false) (hvs : allSome rs = some vs) (hp : c.isParam f = false)
    (ihts : M5 c σ ts rs) (ihf : M1 c f vs r) : M4 c σ (.app f ts) r := by
  intro r' h'
  cases h' with
  | ctor h => rw [hk] at h; cases h
  | hook _ h => rw [hhk] at h; cases h
  | param _ _ h => rw [hp] at h; cases h
  | call _ _ hts' hvs' hf' _ =>
    have := ihts _ hts'; subst this
    rw [hvs] at hvs'; cases hvs'
    exact ihf _ hf'
  | callUndef _ _ hts' hvs' _ =>
    have := ihts _ hts'; subst this
    rw [hvs] at hvs'; cases hvs'

theorem case_callUndef {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = false) (hhk : isHook f = false) (hvs : allSome rs = none)
    (hp : c.isParam f = false) (ihts : M5 c σ ts rs) : M4 c σ (.app f ts) none := by
  intro r' h'
  cases h' with
  | ctor h => rw [hk] at h; cases h
  | hook _ h => rw [hhk] at h; cases h
  | param _ _ h => rw [hp] at h; cases h
  | call _ _ hts' hvs' _ _ =>
    have := ihts _ hts'; subst this
    rw [hvs] at hvs'; cases hvs'
  | callUndef => rfl

theorem case_cons {σ : Subst} {t : Term} {ts : List Term} {r : Option GroundTerm}
    {rs : List (Option GroundTerm)} (ih1 : M4 c σ t r) (ih2 : M5 c σ ts rs) :
    M5 c σ (t :: ts) (r :: rs) := by
  intro rs' h'
  cases h' with
  | cons h1 h2 => rw [ih1 _ h1, ih2 _ h2]

end EvalFunctional

open EvalFunctional in
/-- A function has one result at each argument list. -/
theorem Eval.functional {c : Semantics} (hmi : MatchIndependentAll c) {f : Sym}
    {vs : List GroundTerm} {r r' : Option GroundTerm} (h : Eval c f vs r) (h' : Eval c f vs r') :
    r = r' :=
  Eval.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (fun hfn hcls _ hσ hmatch hreq hrhs ihpre ihreq ihrhs =>
      case_clause hmi hfn hcls hσ hmatch hreq hrhs ihpre ihreq ihrhs)
    (fun hfn _ ho _ ihnone ihrhs => case_owise hfn ho ihnone ihrhs)
    (fun hfn _ ho ihnone => case_undef hfn ho ihnone)
    (fun _ ih => fun σ ha => ih σ ha.1 ha.2.1 ha.2.2)
    (fun ht _ hr ihe => fun hall => hr (ihe _ (hall _ ht)))
    (fun r' h' => by cases h'; rfl)
    (fun r' h' => by cases h'; rfl)
    (fun _ ih => case_inj ih)
    (fun hk _ ihts => case_ctor hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hk hhk hp hr ihts)
    (fun hk hhk _ hvs _ hp ihts ihf => case_call hk hhk hvs hp ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hk hhk hvs hp ihts)
    (fun rs' h' => by cases h'; rfl)
    (fun _ _ ih1 ih2 => case_cons ih1 ih2)
    h r' h'

open EvalFunctional in
/-- A term has one result under each substitution. -/
theorem EvalTerm.functional {c : Semantics} (hmi : MatchIndependentAll c) {σ : Subst} {t : Term}
    {r r' : Option GroundTerm} (h : EvalTerm c σ t r) (h' : EvalTerm c σ t r') : r = r' :=
  EvalTerm.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (fun hfn hcls _ hσ hmatch hreq hrhs ihpre ihreq ihrhs =>
      case_clause hmi hfn hcls hσ hmatch hreq hrhs ihpre ihreq ihrhs)
    (fun hfn _ ho _ ihnone ihrhs => case_owise hfn ho ihnone ihrhs)
    (fun hfn _ ho ihnone => case_undef hfn ho ihnone)
    (fun _ ih => fun σ ha => ih σ ha.1 ha.2.1 ha.2.2)
    (fun ht _ hr ihe => fun hall => hr (ihe _ (hall _ ht)))
    (fun r' h' => by cases h'; rfl)
    (fun r' h' => by cases h'; rfl)
    (fun _ ih => case_inj ih)
    (fun hk _ ihts => case_ctor hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hk hhk hp hr ihts)
    (fun hk hhk _ hvs _ hp ihts ihf => case_call hk hhk hvs hp ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hk hhk hvs hp ihts)
    (fun rs' h' => by cases h'; rfl)
    (fun _ _ ih1 ih2 => case_cons ih1 ih2)
    h r' h'

end KCore

#print axioms KCore.Eval.functional
#print axioms KCore.EvalTerm.functional
