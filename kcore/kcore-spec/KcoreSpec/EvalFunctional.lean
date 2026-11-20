/-
  KCore. Evaluation has one result where clauses of one priority are coherent.

  `Eval` reads no order among the clauses of one priority, so it is not functional by construction:
  two clauses of one priority, or two matches of one clause, may both apply at an argument list.
  Clauses of different priorities never compete (the larger one's derivation has the smaller one
  failing, and a clause that applies does not fail). `Coherent` says that two clauses of one
  priority give one result where both decide (both apply, and no clause of a smaller priority
  applies, `Clause.DecidesAt`); with every such pair coherent (`CoherentAll`), a function has one
  result at each argument list (`Eval.functional`, `fnDet_of_coherent`). No sorting hypothesis is
  needed. Where every function has one result (`FnDet`), so does every term
  (`EvalTerm.functional_of_fnDet`). The definitions are in EvalFunctionalDefs.lean.

  A clause with existential variables has its results by `Eval.clauseEx` and `Eval.exNone`
  (`Clause.Res`). A derivation by `Eval.exNone` holds no derivation for the clause's right-hand
  side or `ensures` at its match (an instance that fails by its predicate evaluates neither), so
  for such a clause `Coherent` grants nothing about them at the match: it grants that each instance
  is decided by terms with one result (`InstDet`), which is what the derivations of the instances
  (`InstIs`) give the induction.

  The shape of `Coherent` is what the proof, an induction on the first derivation, has in hand:
  - the same instance of one right-hand side and one `ensures` (first alternative) is what a
    syntactic check shows; the induction hypotheses for the first clause's right-hand side and
    `ensures` turn it into one result;
  - one result of the two clauses at their matches (second alternative, `Clause.Res`: without
    existential variables the right-hand side's where the `ensures` is `true` and the right side's
    predicate holds, none where the `ensures` is something else) is the semantic statement, for a
    pair no check confirms; it is asked only where both clauses decide, since each `Eval`
    derivation by a clause has every clause of a smaller priority failing;
  - every term inside the first clause's `requires` has one result under its match, and where it
    has no existential variable so does every term inside its `ensures`, and inside its
    right-hand side where its `ensures` is `true` (`HDet`): evaluation is strict, so the first
    derivation holds a derivation for each of them, and the induction hypothesis covers them.
    Nothing is available for the second clause's terms.

  `MatchIndependent` (a clause against itself) and `ClausesAgree` (two clauses of one function)
  are its instances, the obligations `Obligations` names (Obligations.lean).
-/
import KcoreSpec.HoldsCongr

set_option autoImplicit false

namespace KCore

open KCore.Exec

namespace EvalFunctional

variable {c : Semantics}

abbrev M1 (c : Semantics) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ r', Eval c f vs r' → r = r'
abbrev M2 (c : Semantics) (vs : List GroundTerm) (cl : Clause) : Prop :=
  ∀ σ, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs →
    (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) →
    Holds c cl.vars.length σ cl.pre true → False
abbrev M3 (c : Semantics) (σ : Subst) (cl : Clause) : Prop :=
  (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) →
    Holds c cl.vars.length σ cl.pre true → False
abbrev M4 (c : Semantics) (σ : Subst) (t : Term) (r : Option GroundTerm) : Prop :=
  (∀ r', EvalTerm c σ t r' → r = r') ∧ HDet c σ t
abbrev M5 (c : Semantics) (σ : Subst) (ts : List Term) (rs : List (Option GroundTerm)) : Prop :=
  (∀ rs', EvalTerms c σ ts rs' → rs = rs') ∧ ∀ u ∈ subtermsList ts, Fun c σ u
abbrev M6 (c : Semantics) (n : Nat) (σ : Subst) (p : Cond) (b : Bool) : Prop :=
  ∀ b', Holds c n σ p b' → b = b'

theorem mk4 {σ : Subst} {t : Term} {r : Option GroundTerm}
    (top : ∀ r', EvalTerm c σ t r' → r = r')
    (sub : ∀ u ∈ subterms t, u = t ∨ Fun c σ u) : M4 c σ t r :=
  ⟨top, fun u hu => (sub u hu).elim (fun h => h ▸ fun _ _ h1 h2 => (top _ h1).symm.trans (top _ h2)) id⟩

/-- A clause that applies under σ, its `requires` having one result there, does not fail. -/
theorem not_fails {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (ihpre : M6 c cl.vars.length σ cl.pre true) (hf : Fails c vs cl) :
    False := by
  cases hf with
  | intro h =>
    cases h σ (hσ.at _) hmatch with
    | intro ht he hr => exact hr ((ihreq _ ht).1 _ he).symm
    | pre hf => exact absurd (ihpre _ hf) (by simp)

/-- Two clauses of one function: they compete (`CoherentAll`'s condition), or the one of the
smaller priority is not `aside`, so it is among the other's smaller-priority clauses. -/
theorem compete_or_blocks (cl cl' : Clause) :
    (cl.prio = cl'.prio ∨ (cl.aside = true ∧ cl.prio < cl'.prio) ∨ (cl'.aside = true ∧ cl'.prio < cl.prio)) ∨
    (cl.aside = false ∧ cl.prio < cl'.prio) ∨ (cl'.aside = false ∧ cl'.prio < cl.prio) := by
  rcases Nat.lt_trichotomy cl.prio cl'.prio with h | h | h
  · cases ha : cl.aside
    · exact .inr (.inl ⟨rfl, h⟩)
    · exact .inl (.inr (.inl ⟨rfl, h⟩))
  · exact .inl (.inl h)
  · cases ha : cl'.aside
    · exact .inr (.inr ⟨rfl, h⟩)
    · exact .inl (.inr (.inr ⟨rfl, h⟩))

/-- The result of a derivation by `Eval.clauseEx` is a result of its clause at its match. -/
theorem res_clauseEx {cl : Clause} {σ : Subst} {v : GroundTerm} (hσ : c.WellSorted cl.vars σ)
    (hne : cl.exs ≠ []) (hrhs : EvalTerm c σ cl.rhs (some v))
    (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c cl.vars.length σ cl.post true)
    (hall : ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl (some v)) :
    cl.Res c σ (some v) :=
  .inr ⟨hne, .inl ⟨σ, v, AgreeOff.refl _ _, hσ, ⟨hrhs, hens, hpost⟩, hall, rfl⟩⟩

/-- What a derivation of `InstFails` gives: the part of the instance that fails, with one result. -/
abbrev M7 (c : Semantics) (σ : Subst) (cl : Clause) : Prop :=
  (∃ t w, cl.ens = some t ∧ EvalTerm c σ t w ∧ w ≠ some (bool true) ∧ HDet c σ t) ∨
  (Holds c cl.vars.length σ cl.post false ∧ M6 c cl.vars.length σ cl.post false) ∨
  (EvalTerm c σ cl.rhs none ∧ HDet c σ cl.rhs)


/-- A clause that applies at a match well sorted on the left side's variables applies at each of
the match's instances, which is the match on the left side's variables. -/
theorem at_ext {cl : Clause} {σ σ₁ : Subst} {vs : List GroundTerm}
    (ha : AgreeOff cl.exsFree σ σ₁) (hw : c.WellSorted cl.vars σ₁) (hm : PatVals c σ cl.pats vs)
    (hq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true) :
    cl.AppliesAt c σ₁ vs ∧ ∀ i ∈ cl.leftVars, σ₁.lookup i = σ.lookup i := by
  have hl : ∀ i ∈ cl.leftVars, σ₁.lookup i = σ.lookup i := fun i hi => ha i (by simp [Clause.exsFree, hi])
  exact ⟨⟨hw.at _, PatVals.congr_varsRH hm fun j hj => hl j (List.mem_append_left _ hj),
    fun t ht => EvalTerm.congr (hq t ht) fun i hi => (hl i (Clause.req_leftVarsRH ht i hi)).symm,
    Holds.congr_NI hpre fun j hj => (hl j (Clause.pre_leftVarsRH j hj)).symm⟩, hl⟩

/-- The result of a derivation by `Eval.exNone` is a result of its clause at each instance of its
match: the instances of the instance are the match's. -/
theorem res_exNone {cl : Clause} {σ σ₁ : Subst} (hne : cl.exs ≠ [])
    (ha : AgreeOff cl.exsFree σ σ₁) (hw : c.WellSorted cl.vars σ₁)
    (hall : ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl none) :
    cl.Res c σ₁ none :=
  .inr ⟨hne, .inr ⟨rfl, ⟨σ₁, AgreeOff.refl _ _, hw⟩, fun σ₂ ha₂ hw₂ => hall σ₂ (ha.trans ha₂) hw₂⟩⟩

/-- A derivation by a clause, the first, applying under σ and not failing, with the induction
hypothesis for the clauses of a smaller priority, against a second derivation at the same argument
list, given the first clause's result `r` at σ (`hres`) and what `Coherent` asks of it there
(`hqd`, `hrd`, `hed`, `hid`): where the two clauses are the same instance (`hsame`), or by the two
results. A second derivation by `Eval.exNone` is read at one of its instances, where its clause
applies and has the result none. -/
theorem case_by {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    {r : Option GroundTerm} (hco : CoherentAll c)
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses) (ha : cl.AppliesAt c σ vs)
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
    (hnf : Fails c vs cl → False)
    (ihprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → M2 c vs cl')
    (hqd : ∀ t, cl.req = some t → HDet c σ t)
    (hrd : cl.exs = [] → (∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) → HDet c σ cl.rhs)
    (hed : cl.exs = [] → ∀ t, cl.ens = some t → HDet c σ t)
    (hid : cl.exs ≠ [] → ∀ σ₁, AgreeOff cl.exsFree σ σ₁ → c.WellSorted cl.vars σ₁ → InstDet c cl σ₁)
    (hres : cl.Res c σ r)
    (hsame : ∀ (cl' : Clause) (σ' : Subst) (r' : Option GroundTerm), cl.exs = [] → cl'.exs = [] → cl.rhs = cl'.rhs →
      cl.ens = cl'.ens → (∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) →
      (∀ t, cl.ens = some t → ∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) →
      cl'.Res c σ' r' → r = r') : M1 c f vs r := by
  have key : ∀ (cl' : Clause) (σ' : Subst) (r' : Option GroundTerm), cl' ∈ fn.clauses →
      cl'.AppliesAt c σ' vs → c.WellSortedAt cl'.vars cl'.leftVars σ' →
      (∀ cl'' ∈ fn.clauses, cl''.aside = false → cl''.prio < cl'.prio → Fails c vs cl'') →
      cl'.Res c σ' r' → r = r' := by
    intro cl' σ' r' hmem' ha' hl' hprio' hres'
    rcases compete_or_blocks cl cl' with hcomp | ⟨hna, hlt⟩ | ⟨hna, hgt⟩
    · rcases hco f fn hfn cl hmem cl' hmem' hcomp vs σ σ' ha ha' hqd hrd hed hid
          ⟨f, fn, hfn, hmem, hmem', ⟨ha, hprio⟩, ⟨ha', hprio'⟩⟩ with ⟨hx, hx', he, hee, hv, hve⟩ | hr
      · exact hsame cl' σ' r' hx hx' he hee hv hve hres'
      · exact hr _ _ hres hres'
    · exact (hnf (hprio' _ hmem hna hlt)).elim
    · exact (ihprio _ hmem' hna hgt _ hl' ha'.2.1 ha'.2.2.1 ha'.2.2.2).elim
  intro r' h'
  cases h' with
  | @clause _ _ _ cl' σ' _ hfn' hmem' hσ' hmatch' hreq' hpre' hprio' hex' hrhs' hens' hpost' =>
    rw [hfn] at hfn'; cases hfn'
    exact key cl' σ' r' hmem' ⟨hσ'.at _, hmatch', hreq', hpre'⟩ (hσ'.at _) hprio' (.inl ⟨hex', .inl ⟨hens', hpost', hrhs'⟩⟩)
  | rest hfn' hnone' =>
    rw [hfn] at hfn'; cases hfn'
    exact (hnf (hnone' _ hmem)).elim
  | @ensFails _ _ _ cl' σ' t' w' hfn' hmem' hσ' hmatch' hreq' hpre' hprio' hex' ht' he' hw' =>
    rw [hfn] at hfn'; cases hfn'
    exact key cl' σ' none hmem' ⟨hσ'.at _, hmatch', hreq', hpre'⟩ (hσ'.at _) hprio' (.inl ⟨hex', .inr ⟨t', w', ht', he', hw', rfl⟩⟩)
  | @clauseEx _ _ _ cl' σ' v' hfn' hmem' hσ' hmatch' hreq' hpre' hprio' hne' hrhs' hens' hpost' hall' =>
    rw [hfn] at hfn'; cases hfn'
    exact key cl' σ' (some v') hmem' ⟨hσ'.at _, hmatch', hreq', hpre'⟩ (hσ'.at _) hprio' (res_clauseEx hσ' hne' hrhs' hens' hpost' hall')
  | @exNone _ _ _ cl' σ' hfn' hmem' hne' _ hmatch' hreq' hpre' hprio' hsome' hall' =>
    rw [hfn] at hfn'; cases hfn'
    obtain ⟨σ₁, ha₁, hw₁⟩ := hsome'
    exact key cl' σ₁ none hmem' (at_ext ha₁ hw₁ hmatch' hreq' hpre').1 (hw₁.at _) hprio' (res_exNone hne' ha₁ hw₁ hall')

/-- A clause that applies under σ, well sorted on the left side's variables, its `requires` and
predicate having one result there, does not fail. -/
theorem not_fails_at {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    (hσ : c.WellSortedAt cl.vars cl.leftVars σ) (hmatch : PatVals c σ cl.pats vs)
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (ihpre : M6 c cl.vars.length σ cl.pre true) (hf : Fails c vs cl) : False := by
  cases hf with
  | intro h =>
    cases h σ hσ hmatch with
    | intro ht he hr => exact hr ((ihreq _ ht).1 _ he).symm
    | pre hf => exact absurd (ihpre _ hf) (by simp)

theorem case_rest {f : Sym} {fn : Fn} {vs : List GroundTerm}
    (hfn : c.lookupFn f = some fn)
    (ihnone : ∀ cl ∈ fn.clauses, M2 c vs cl) : M1 c f vs (c.fnRest fn vs) := by
  intro r' h'
  cases h' with
  | clause hfn' hmem' hσ' hmatch' hreq' hpre' _ _ _ _ _ =>
    rw [hfn] at hfn'; cases hfn'
    exact (ihnone _ hmem' _ (hσ'.at _) hmatch' hreq' hpre').elim
  | rest hfn' _ => rw [hfn] at hfn'; cases hfn'; rfl
  | ensFails hfn' hmem' hσ' hmatch' hreq' hpre' _ _ _ _ _ =>
    rw [hfn] at hfn'; cases hfn'
    exact (ihnone _ hmem' _ (hσ'.at _) hmatch' hreq' hpre').elim
  | clauseEx hfn' hmem' hσ' hmatch' hreq' hpre' _ _ _ _ _ _ =>
    rw [hfn] at hfn'; cases hfn'
    exact (ihnone _ hmem' _ (hσ'.at _) hmatch' hreq' hpre').elim
  | exNone hfn' hmem' _ _ hmatch' hreq' hpre' _ hsome' _ =>
    rw [hfn] at hfn'; cases hfn'
    obtain ⟨σ₁, ha, hw⟩ := hsome'
    exact (ihnone _ hmem' _ (wellSortedAt_left_of_ext ha hw) hmatch' hreq' hpre').elim

theorem case_inj {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm}
    (ih : M4 c σ t r) : M4 c σ (.inj a b t) (r.map (injNormal a b)) :=
  mk4 (fun r' h' => by cases h' with | inj h'' => rw [ih.1 _ h''])
    (fun u hu => by
      simp only [subterms, List.mem_cons] at hu
      exact hu.imp id (ih.2 u))

theorem sub_app {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (ihts : M5 c σ ts rs) : ∀ u ∈ subterms (.app f ts), u = .app f ts ∨ Fun c σ u :=
  fun u hu => by
    simp only [subterms, List.mem_cons] at hu
    exact hu.imp id (ihts.2 u)

theorem case_ctor {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = true) (ihts : M5 c σ ts rs) :
    M4 c σ (.app f ts) ((allSome rs).map (.ctor f)) :=
  mk4 (fun r' h' => by
    cases h' with
    | ctor _ hts' => rw [ihts.1 _ hts']
    | hook h => rw [hk] at h; cases h
    | param h => rw [hk] at h; cases h
    | call h => rw [hk] at h; cases h
    | callUndef h => rw [hk] at h; cases h
    | ovl h => rw [hk] at h; cases h
    | ovlFn h => rw [hk] at h; cases h) (sub_app ihts)

theorem case_hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = true)
    (hh : ∀ vs, allSome rs = some vs → c.hookRes f vs = some r) (hund : allSome rs = none → r = none)
    (ihts : M5 c σ ts rs) : M4 c σ (.app f ts) r :=
  mk4 (fun r' h' => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ _ hts' hh' hund' =>
      have := ihts.1 _ hts'; subst this
      cases hall : allSome rs with
      | none => rw [hund hall, hund' hall]
      | some vs => exact Option.some.inj ((hh vs hall).symm.trans (hh' vs hall))
    | param _ h => rw [hhk] at h; cases h
    | call _ h => rw [hhk] at h; cases h
    | callUndef _ h => rw [hhk] at h; cases h
    | ovl _ ho => rw [(c.isOvl_parts ho).2.1] at hhk; cases hhk
    | ovlFn _ ho => rw [(c.isOvl_parts ho).2.1] at hhk; cases hhk) (sub_app ihts)

theorem case_param {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = false)
    (hp : c.isParam f = true) (hr : r = (allSome rs).bind (c.paramVal f))
    (ihts : M5 c σ ts rs) : M4 c σ (.app f ts) r :=
  mk4 (fun r' h' => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ h => rw [hhk] at h; cases h
    | param _ _ _ hts' hr' => have := ihts.1 _ hts'; subst this; rw [hr, hr']
    | call _ _ _ _ _ h => rw [hp] at h; cases h
    | callUndef _ _ _ _ h => rw [hp] at h; cases h
    | ovl _ ho => rw [(c.isOvl_parts ho).2.2.1] at hp; cases hp
    | ovlFn _ ho => rw [(c.isOvl_parts ho).2.2.1] at hp; cases hp) (sub_app ihts)

theorem case_call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {vs : List GroundTerm} {r : Option GroundTerm} (hk : c.isCtor f = false)
    (hhk : isHook f = false) (hvs : allSome rs = some vs) (hp : c.isParam f = false)
    (hno : c.isOvl f = false) (ihts : M5 c σ ts rs) (ihf : M1 c f vs r) : M4 c σ (.app f ts) r :=
  mk4 (fun r' h' => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ h => rw [hhk] at h; cases h
    | param _ _ h => rw [hp] at h; cases h
    | call _ _ hts' hvs' hf' _ =>
      have := ihts.1 _ hts'; subst this
      rw [hvs] at hvs'; cases hvs'
      exact ihf _ hf'
    | callUndef _ _ hts' hvs' _ =>
      have := ihts.1 _ hts'; subst this
      rw [hvs] at hvs'; cases hvs'
    | ovl _ ho => rw [hno] at ho; cases ho
    | ovlFn _ ho => rw [hno] at ho; cases ho) (sub_app ihts)

theorem case_callUndef {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = false) (hhk : isHook f = false) (hvs : allSome rs = none)
    (hp : c.isParam f = false) (ihts : M5 c σ ts rs) : M4 c σ (.app f ts) none :=
  mk4 (fun r' h' => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ h => rw [hhk] at h; cases h
    | param _ _ h => rw [hp] at h; cases h
    | call _ _ hts' hvs' _ _ =>
      have := ihts.1 _ hts'; subst this
      rw [hvs] at hvs'; cases hvs'
    | callUndef => rfl
    | ovl _ _ hts' => have := ihts.1 _ hts'; subst this; rw [hvs]; rfl
    | ovlFn _ _ hts' hvs' => have := ihts.1 _ hts'; subst this; rw [hvs] at hvs'; cases hvs') (sub_app ihts)

theorem case_ovl {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = false) (ho : c.isOvl f = true)
    (hnf : ∀ vs, allSome rs = some vs → c.fnCover f vs = none) (ihts : M5 c σ ts rs) :
    M4 c σ (.app f ts) ((allSome rs).map (c.norm f)) :=
  have hp := c.isOvl_parts ho
  mk4 (fun r' h' => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ h => rw [hp.2.1] at h; cases h
    | param _ _ h => rw [hp.2.2.1] at h; cases h
    | call _ _ _ _ hf' _ => rw [hf'.isOvl_false] at ho; cases ho
    | callUndef _ _ hts' hvs' _ => have := ihts.1 _ hts'; subst this; rw [hvs']; rfl
    | ovl _ _ hts' => have := ihts.1 _ hts'; subst this; rfl
    | ovlFn _ _ hts' hvs' _ hcov' =>
      have := ihts.1 _ hts'; subst this
      rw [hnf _ hvs'] at hcov'; cases hcov') (sub_app ihts)

theorem case_ovlFn {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {vs : List GroundTerm} {o : OvlSig} {kg : CtorSig} {r : Option GroundTerm}
    (hk : c.isCtor f = false) (ho : c.isOvl f = true) (hvs : allSome rs = some vs)
    (hlo : c.lookupOvl f = some o) (hcov : c.fnCover f vs = some kg) (ihts : M5 c σ ts rs)
    (ihf : M1 c kg.name (stripAll kg.args o.sig.args vs) r) :
    M4 c σ (.app f ts) (r.map (lift kg.result o.sig.result)) :=
  have hp := c.isOvl_parts ho
  mk4 (fun r' h' => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ h => rw [hp.2.1] at h; cases h
    | param _ _ h => rw [hp.2.2.1] at h; cases h
    | call _ _ _ _ hf' _ => rw [hf'.isOvl_false] at ho; cases ho
    | callUndef _ _ hts' hvs' _ => have := ihts.1 _ hts'; subst this; rw [hvs] at hvs'; cases hvs'
    | ovl _ _ hts' hnf' => have := ihts.1 _ hts'; subst this; rw [hnf' _ hvs] at hcov; cases hcov
    | ovlFn _ _ hts' hvs' hlo' hcov' hf' =>
      have := ihts.1 _ hts'; subst this
      rw [hvs] at hvs'; cases hvs'
      rw [hlo] at hlo'; cases hlo'
      rw [hcov] at hcov'; cases hcov'
      rw [ihf _ hf']) (sub_app ihts)

theorem case_cons {σ : Subst} {t : Term} {ts : List Term} {r : Option GroundTerm}
    {rs : List (Option GroundTerm)} (ih1 : M4 c σ t r) (ih2 : M5 c σ ts rs) :
    M5 c σ (t :: ts) (r :: rs) :=
  ⟨fun rs' h' => by cases h' with | cons h1 h2 => rw [ih1.1 _ h1, ih2.1 _ h2],
   fun u hu => by
    simp only [subtermsList, List.mem_append] at hu
    exact hu.elim (ih1.2 u) (ih2.2 u)⟩

theorem leaf {σ : Subst} {t : Term} {r : Option GroundTerm} (hs : subterms t = [t])
    (top : ∀ r', EvalTerm c σ t r' → r = r') : M4 c σ t r :=
  mk4 top fun u hu => by rw [hs, List.mem_singleton] at hu; exact .inl hu

/-! ### The cases of `Holds`: a condition has one truth value where its terms have one result -/

theorem caseH_not {n : Nat} {σ : Subst} {p : Cond} {b : Bool} (ih : M6 c n σ p b) :
    M6 c n σ (.not p) (!b) := by
  intro b' h'; cases h' with | not h2 => rw [ih _ h2]

theorem caseH_and {n : Nat} {σ : Subst} {p q : Cond} {b b' : Bool} (ih : M6 c n σ p b)
    (ih' : M6 c n σ q b') : M6 c n σ (.and p q) (b && b') := by
  intro b'' h'; cases h' with | and h2 h2' => rw [ih _ h2, ih' _ h2']

theorem caseH_or {n : Nat} {σ : Subst} {p q : Cond} {b b' : Bool} (ih : M6 c n σ p b)
    (ih' : M6 c n σ q b') : M6 c n σ (.or p q) (b || b') := by
  intro b'' h'; cases h' with | or h2 h2' => rw [ih _ h2, ih' _ h2']

theorem caseH_implies {n : Nat} {σ : Subst} {p q : Cond} {b b' : Bool} (ih : M6 c n σ p b)
    (ih' : M6 c n σ q b') : M6 c n σ (.implies p q) (!b || b') := by
  intro b'' h'; cases h' with | implies h2 h2' => rw [ih _ h2, ih' _ h2']

theorem caseH_ceil {n : Nat} {σ : Subst} {s : Srt} {t : Term} {r : Option GroundTerm}
    (ih : M4 c σ t r) : M6 c n σ (.ceil s t) r.isSome := by
  intro b' h'; cases h' with | ceil h2 => rw [ih.1 _ h2]

theorem caseH_equals {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {r r' : Option GroundTerm}
    (ih : M4 c σ t r) (ih' : M4 c σ u r') : M6 c n σ (.equals s t u) (sameResult r r') := by
  intro b' h'; cases h' with | equals h2 h2' => rw [ih.1 _ h2, ih'.1 _ h2']

theorem caseH_mem {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {r r' : Option GroundTerm}
    (ih : M4 c σ t r) (ih' : M4 c σ u r') :
    M6 c n σ (.mem s t u) (r.isSome && sameResult r r') := by
  intro b' h'; cases h' with | mem h2 h2' => rw [ih.1 _ h2, ih'.1 _ h2']

theorem caseH_exNone {n : Nat} {σ : Subst} {ys : List Srt} {s : Srt} {p t : Term} {body : Cond}
    (ih : M4 c σ t none) : M6 c n σ (.exMatch ys s p t body) false := by
  intro b' h'
  cases h' with
  | exNone _ => rfl
  | exSome g h2 _ _ => cases ih.1 _ h2

theorem caseH_exSome {n : Nat} {σ : Subst} {ys : List Srt} {s : Srt} {p t : Term} {body : Cond}
    {v : GroundTerm} {b : Bool} {g : Subst → Bool}
    (hr : b = true ↔ ∃ σ', Extends c n ys σ σ' ∧ PatVal c σ' p v ∧ g σ' = true)
    (ih : M4 c σ t (some v))
    (ihb : ∀ σ', Extends c n ys σ σ' → PatVal c σ' p v → M6 c (n + ys.length) σ' body (g σ')) :
    M6 c n σ (.exMatch ys s p t body) b := by
  intro b' h'
  cases h' with
  | exNone h2 => cases ih.1 _ h2
  | exSome g' h2 hb' hr' =>
    cases ih.1 _ h2
    rw [Bool.eq_iff_iff, hr, hr']
    exact ⟨fun ⟨σ', hx, hm, hg⟩ => ⟨σ', hx, hm, (ihb σ' hx hm _ (hb' σ' hx hm)).symm.trans hg⟩,
      fun ⟨σ', hx, hm, hg⟩ => ⟨σ', hx, hm, (ihb σ' hx hm _ (hb' σ' hx hm)).trans hg⟩⟩

theorem caseH_ex {n : Nat} {σ : Subst} {s : Srt} {body : Cond} {b : Bool} {g : Subst → Bool}
    (hr : b = true ↔ ∃ σ', Extends c n [s] σ σ' ∧ g σ' = true)
    (ihb : ∀ σ', Extends c n [s] σ σ' → M6 c (n + 1) σ' body (g σ')) :
    M6 c n σ (.ex s body) b := by
  intro b' h'
  cases h' with
  | ex g' hb' hr' =>
    rw [Bool.eq_iff_iff, hr, hr']
    exact ⟨fun ⟨σ', hx, hg⟩ => ⟨σ', hx, (ihb σ' hx _ (hb' σ' hx)).symm.trans hg⟩,
      fun ⟨σ', hx, hg⟩ => ⟨σ', hx, (ihb σ' hx _ (hb' σ' hx)).trans hg⟩⟩

theorem caseH_all {n : Nat} {σ : Subst} {s : Srt} {body : Cond} {b : Bool} {g : Subst → Bool}
    (hr : b = true ↔ ∀ σ', Extends c n [s] σ σ' → g σ' = true)
    (ihb : ∀ σ', Extends c n [s] σ σ' → M6 c (n + 1) σ' body (g σ')) :
    M6 c n σ (.all s body) b := by
  intro b' h'
  cases h' with
  | all g' hb' hr' =>
    rw [Bool.eq_iff_iff, hr, hr']
    exact ⟨fun hall σ' hx => (ihb σ' hx _ (hb' σ' hx)).symm.trans (hall σ' hx),
      fun hall σ' hx => (ihb σ' hx _ (hb' σ' hx)).trans (hall σ' hx)⟩

end EvalFunctional

open EvalFunctional in
/-- **A function has one result at each argument list** when the clauses that compete are
coherent. For a derivation by a clause with existential variables, what `Coherent` asks of each
instance (`InstDet`) is the induction hypothesis on the derivation's instances; a derivation by
`Eval.exNone` is read at one of its instances. -/
theorem Eval.functional {c : Semantics} (hco : CoherentAll c) {f : Sym}
    {vs : List GroundTerm} {r r' : Option GroundTerm} (h : Eval c f vs r) (h' : Eval c f vs r') :
    r = r' :=
  Eval.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun n σ p b _ => M6 c n σ p b)
    (motive_7 := fun σ cl _ => M7 c σ cl) (motive_8 := fun σ cl _ _ => InstDet c cl σ)
    -- clause
    (fun {f fn vs cl σ r} hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost ihreq ihpre ihprio ihrhs ihens _ =>
      case_by hco hfn hmem ⟨hσ.at _, hmatch, hreq, hpre⟩ hprio (not_fails hσ hmatch ihreq ihpre) ihprio
        (fun t ht => (ihreq t ht).2) (fun _ _ => ihrhs.2) (fun _ t ht => (ihens t ht).2) (fun hne => absurd hex hne)
        (.inl ⟨hex, .inl ⟨hens, hpost, hrhs⟩⟩)
        fun cl' σ' r' _ hx' he hee hv hve hres' => by
          rcases (Clause.res_noExs hx').mp hres' with ⟨-, -, hrhs'⟩ | ⟨t', w', ht', he', hw', rfl⟩
          · rw [← he] at hrhs'
            exact ihrhs.1 r' (EvalTerm.congr hrhs' fun i hi => (hv i hi).symm)
          · rw [← hee] at ht'
            exact (hw' ((ihens t' ht').1 w' (EvalTerm.congr he' fun i hi => (hve t' ht' i hi).symm)).symm).elim)
    (fun hfn _ ihnone => case_rest hfn ihnone)
    -- ensFails
    (fun {f fn vs cl σ t w} hfn hmem hσ hmatch hreq hpre hprio hex ht he hw ihreq ihpre ihprio ihe =>
      have hnot : ¬ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) := fun h => hw (ihe.1 _ (h t ht))
      case_by hco hfn hmem ⟨hσ.at _, hmatch, hreq, hpre⟩ hprio (not_fails hσ hmatch ihreq ihpre) ihprio
        (fun t ht => (ihreq t ht).2) (fun _ h => (hnot h).elim)
        (fun _ t' ht'' => by rw [ht] at ht''; cases ht''; exact ihe.2) (fun hne => absurd hex hne)
        (.inl ⟨hex, .inr ⟨t, w, ht, he, hw, rfl⟩⟩)
        fun cl' σ' r' _ hx' _ hee _ hve hres' => by
          rcases (Clause.res_noExs hx').mp hres' with ⟨hens', -, -⟩ | ⟨_, _, _, _, _, rfl⟩
          · exact (hnot fun t'' ht'' =>
              EvalTerm.congr (hens' t'' (hee ▸ ht'')) fun i hi => (hve t'' ht'' i hi).symm).elim
          · rfl)
    -- clauseEx: the premise on the instances is the induction hypothesis on `hall`
    (fun {f fn vs cl σ v} hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall ihreq ihpre ihprio _ _ _ ihall =>
      case_by hco hfn hmem ⟨hσ.at _, hmatch, hreq, hpre⟩ hprio (not_fails hσ hmatch ihreq ihpre) ihprio
        (fun t ht => (ihreq t ht).2) (fun hx => absurd hx hne) (fun hx => absurd hx hne)
        (fun _ σ₁ ha₁ hw₁ => ihall σ₁ ha₁ hw₁) (res_clauseEx hσ hne hrhs hens hpost hall)
        fun _ _ _ hx _ _ _ _ _ _ => absurd hx hne)
    -- exNone: at an instance, which is the match on the left side
    (fun {f fn vs cl σ} hfn hmem hne _ hmatch hreq hpre hprio hsome hall ihreq ihpre ihprio ihall =>
      let ⟨σ₁, ha₁, hw₁⟩ := hsome
      have hx := at_ext ha₁ hw₁ hmatch hreq hpre
      case_by hco hfn hmem hx.1 hprio
        (not_fails_at (wellSortedAt_left_of_ext ha₁ hw₁) hmatch ihreq ihpre) ihprio
        (fun t ht u hu => Fun.congr (fun i hi => hx.2 i (Clause.req_leftVarsRH ht i (varOccs_subterms hu i hi)))
          ((ihreq t ht).2 u hu))
        (fun hx => absurd hx hne) (fun hx => absurd hx hne)
        (fun _ σ₂ ha₂ hw₂ => ihall σ₂ (ha₁.trans ha₂) hw₂) (res_exNone hne ha₁ hw₁ hall)
        fun _ _ _ hx _ _ _ _ _ _ => absurd hx hne)
    (fun _ ih => fun σ hw hp hq hpre => ih σ hw hp hq hpre)
    (fun ht _ hr ihe => fun hall _ => hr (ihe.1 _ (hall _ ht)))
    (fun _ ih => fun _ hpre => absurd (ih _ hpre) (by simp))
    (leaf rfl fun r' h' => by cases h'; rfl)
    (leaf rfl fun r' h' => by cases h'; rfl)
    (fun _ ih => case_inj ih)
    (fun hk _ ihts => case_ctor hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hk hhk hp hr ihts)
    (fun hk hhk _ hvs hf hp ihts ihf => case_call hk hhk hvs hp hf.isOvl_false ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hk hhk hvs hp ihts)
    (fun hk ho _ hnf ihts => case_ovl hk ho hnf ihts)
    (fun hk ho _ hvs hlo hcov _ ihts ihf => case_ovlFn hk ho hvs hlo hcov ihts ihf)
    ⟨fun rs' h' => by cases h'; rfl, fun u hu => by simp [subtermsList] at hu⟩
    (fun _ _ ih1 ih2 => case_cons ih1 ih2)
    (fun b' h' => by cases h'; rfl)
    (fun b' h' => by cases h'; rfl)
    (fun _ ih => caseH_not ih)
    (fun _ _ ih ih' => caseH_and ih ih')
    (fun _ _ ih ih' => caseH_or ih ih')
    (fun _ _ ih ih' => caseH_implies ih ih')
    (fun _ ih => caseH_ceil ih)
    (fun _ _ ih ih' => caseH_equals ih ih')
    (fun _ _ ih ih' => caseH_mem ih ih')
    (fun _ ih => caseH_exNone ih)
    (fun _ _ _ hr ih ihb => caseH_exSome hr ih ihb)
    (fun _ _ hr ihb => caseH_ex hr ihb)
    (fun _ _ hr ihb => caseH_all hr ihb)
    -- InstFails
    (fun ht he hw ihe => .inl ⟨_, _, ht, he, hw, ihe.2⟩)
    (fun h ih => .inr (.inl ⟨h, ih⟩))
    (fun h ih => .inr (.inr ⟨h, ih.2⟩))
    -- InstIs
    (fun hp _ ihp ih => ⟨⟨_, hp, ihp⟩, ih.elim .inl fun ih => ih.elim (fun x => .inr (.inl x.1)) fun x => .inr (.inr (.inl x))⟩)
    (fun hrhs hens hpost ihrhs ihens ihpost =>
      ⟨⟨true, hpost, ihpost⟩, .inr (.inr (.inr ⟨_, hrhs, ihrhs.2, fun t ht => ⟨hens t ht, (ihens t ht).2⟩, hpost⟩))⟩)
    h r' h'

/-- Clauses that compete coherent, every function has at most one result. -/
theorem fnDet_of_coherent {c : Semantics} (hco : CoherentAll c) : FnDet c :=
  fun _ _ _ _ h h' => Eval.functional hco h h'

open EvalFunctional in
/-- A term has one result under each substitution where every function has at most one result;
so does every term inside it. -/
theorem EvalTerm.functional_hdet_of_fnDet {c : Semantics} (hd : FnDet c) {σ : Subst} {t : Term}
    {r : Option GroundTerm} (h : EvalTerm c σ t r) : (∀ r', EvalTerm c σ t r' → r = r') ∧ HDet c σ t :=
  EvalTerm.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun n σ p b _ => M6 c n σ p b)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost _ _ _ _ _ _ => fun r' h' =>
      hd _ _ _ _ (.clause hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost) h')
    (fun hfn hnone _ => fun r' h' => hd _ _ _ _ (.rest hfn hnone) h')
    (fun hfn hmem hσ hmatch hreq hpre hprio hex ht he hw _ _ _ _ => fun r' h' =>
      hd _ _ _ _ (.ensFails hfn hmem hσ hmatch hreq hpre hprio hex ht he hw) h')
    (fun hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall _ _ _ _ _ _ _ => fun r' h' =>
      hd _ _ _ _ (.clauseEx hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall) h')
    (fun hfn hmem hne hσ hmatch hreq hpre hprio hsome hall _ _ _ _ => fun r' h' =>
      hd _ _ _ _ (.exNone hfn hmem hne hσ hmatch hreq hpre hprio hsome hall) h')
    (fun _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ => trivial)
    (leaf rfl fun r' h' => by cases h'; rfl)
    (leaf rfl fun r' h' => by cases h'; rfl)
    (fun _ ih => case_inj ih)
    (fun hk _ ihts => case_ctor hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hk hhk hp hr ihts)
    (fun hk hhk _ hvs hf hp ihts ihf => case_call hk hhk hvs hp hf.isOvl_false ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hk hhk hvs hp ihts)
    (fun hk ho _ hnf ihts => case_ovl hk ho hnf ihts)
    (fun hk ho _ hvs hlo hcov _ ihts ihf => case_ovlFn hk ho hvs hlo hcov ihts ihf)
    ⟨fun rs' h' => by cases h'; rfl, fun u hu => by simp [subtermsList] at hu⟩
    (fun _ _ ih1 ih2 => case_cons ih1 ih2)
    (fun b' h' => by cases h'; rfl)
    (fun b' h' => by cases h'; rfl)
    (fun _ ih => caseH_not ih)
    (fun _ _ ih ih' => caseH_and ih ih')
    (fun _ _ ih ih' => caseH_or ih ih')
    (fun _ _ ih ih' => caseH_implies ih ih')
    (fun _ ih => caseH_ceil ih)
    (fun _ _ ih ih' => caseH_equals ih ih')
    (fun _ _ ih ih' => caseH_mem ih ih')
    (fun _ ih => caseH_exNone ih)
    (fun _ _ _ hr ih ihb => caseH_exSome hr ih ihb)
    (fun _ _ hr ihb => caseH_ex hr ihb)
    (fun _ _ hr ihb => caseH_all hr ihb)
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    h

/-- A term has one result under each substitution where every function has at most one
result. -/
theorem EvalTerm.functional_of_fnDet {c : Semantics} (hd : FnDet c) {σ : Subst} {t : Term}
    {r r' : Option GroundTerm} (h : EvalTerm c σ t r) (h' : EvalTerm c σ t r') : r = r' :=
  (EvalTerm.functional_hdet_of_fnDet hd h).1 r' h'

open EvalFunctional in
/-- A condition has one truth value under each substitution where every function has at most one
result. -/
theorem Holds.functional_of_fnDet {c : Semantics} (hd : FnDet c) {n : Nat} {σ : Subst} {p : Cond}
    {b b' : Bool} (h : Holds c n σ p b) (h' : Holds c n σ p b') : b = b' :=
  Holds.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun n σ p b _ => M6 c n σ p b)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost _ _ _ _ _ _ => fun r' h' =>
      hd _ _ _ _ (.clause hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost) h')
    (fun hfn hnone _ => fun r' h' => hd _ _ _ _ (.rest hfn hnone) h')
    (fun hfn hmem hσ hmatch hreq hpre hprio hex ht he hw _ _ _ _ => fun r' h' =>
      hd _ _ _ _ (.ensFails hfn hmem hσ hmatch hreq hpre hprio hex ht he hw) h')
    (fun hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall _ _ _ _ _ _ _ => fun r' h' =>
      hd _ _ _ _ (.clauseEx hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall) h')
    (fun hfn hmem hne hσ hmatch hreq hpre hprio hsome hall _ _ _ _ => fun r' h' =>
      hd _ _ _ _ (.exNone hfn hmem hne hσ hmatch hreq hpre hprio hsome hall) h')
    (fun _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ => trivial)
    (leaf rfl fun r' h' => by cases h'; rfl)
    (leaf rfl fun r' h' => by cases h'; rfl)
    (fun _ ih => case_inj ih)
    (fun hk _ ihts => case_ctor hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hk hhk hp hr ihts)
    (fun hk hhk _ hvs hf hp ihts ihf => case_call hk hhk hvs hp hf.isOvl_false ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hk hhk hvs hp ihts)
    (fun hk ho _ hnf ihts => case_ovl hk ho hnf ihts)
    (fun hk ho _ hvs hlo hcov _ ihts ihf => case_ovlFn hk ho hvs hlo hcov ihts ihf)
    ⟨fun rs' h' => by cases h'; rfl, fun u hu => by simp [subtermsList] at hu⟩
    (fun _ _ ih1 ih2 => case_cons ih1 ih2)
    (fun b' h' => by cases h'; rfl)
    (fun b' h' => by cases h'; rfl)
    (fun _ ih => caseH_not ih)
    (fun _ _ ih ih' => caseH_and ih ih')
    (fun _ _ ih ih' => caseH_or ih ih')
    (fun _ _ ih ih' => caseH_implies ih ih')
    (fun _ ih => caseH_ceil ih)
    (fun _ _ ih ih' => caseH_equals ih ih')
    (fun _ _ ih ih' => caseH_mem ih ih')
    (fun _ ih => caseH_exNone ih)
    (fun _ _ _ hr ih ihb => caseH_exSome hr ih ihb)
    (fun _ _ hr ihb => caseH_ex hr ihb)
    (fun _ _ hr ihb => caseH_all hr ihb)
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    h b' h'

/-- A term has one result under each substitution when the clauses that compete are coherent; so
does every term inside it. -/
theorem EvalTerm.functional_hdet {c : Semantics} (hco : CoherentAll c) {σ : Subst} {t : Term}
    {r : Option GroundTerm} (h : EvalTerm c σ t r) : (∀ r', EvalTerm c σ t r' → r = r') ∧ HDet c σ t :=
  EvalTerm.functional_hdet_of_fnDet (fnDet_of_coherent hco) h

/-- A term has one result under each substitution when the clauses that compete are coherent. -/
theorem EvalTerm.functional {c : Semantics} (hco : CoherentAll c) {σ : Subst} {t : Term}
    {r r' : Option GroundTerm} (h : EvalTerm c σ t r) (h' : EvalTerm c σ t r') : r = r' :=
  (EvalTerm.functional_hdet hco h).1 r' h'

/-- A condition has one truth value under each substitution when the clauses that compete are
coherent. -/
theorem Holds.functional {c : Semantics} (hco : CoherentAll c) {n : Nat} {σ : Subst} {p : Cond}
    {b b' : Bool} (h : Holds c n σ p b) (h' : Holds c n σ p b') : b = b' :=
  Holds.functional_of_fnDet (fnDet_of_coherent hco) h h'

end KCore
