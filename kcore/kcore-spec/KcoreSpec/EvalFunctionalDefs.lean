/-
  KCore. What it is for the clauses of a function to give one result: the definitions.

  `Eval` reads no order among the clauses of one priority, so it is not functional by construction:
  two clauses of one priority, or two matches of one clause, may both apply at an argument list.
  `Coherent` says that two clauses that compete give one result where both decide (both apply, and
  no clause of a smaller priority applies, `Clause.Decides`); `CoherentAll` says it of every such
  pair, `MatchIndependent` of a clause against itself, `FnDet` that every function has at most one
  result and `FnSolves` that evaluation solves the clauses' equations. That `CoherentAll` gives
  `FnDet` is `fnDet_of_coherent` (EvalFunctional.lean), where the shape of `Coherent` is explained.
-/
import KcoreSpec.EvalSound

set_option autoImplicit false

namespace KCore

open KCore.Exec

/-- The clause applies at `vs` under σ: σ is well sorted, the patterns denote `vs`, the
`requires` evaluates to `true`, and the predicate `pre` is true. -/
def Clause.AppliesAt (c : Semantics) (cl : Clause) (σ : Subst) (vs : List GroundTerm) : Prop :=
  c.WellSorted cl.vars σ ∧ PatVals c σ cl.pats vs ∧
    (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c cl.vars.length σ cl.pre true

mutual
  /-- A term and the terms inside it. Evaluation is strict, so a derivation for a term holds one
  for each of them. -/
  def subterms : Term → List Term
    | .var i => [.var i]
    | .dv s l => [.dv s l]
    | .inj a b t => .inj a b t :: subterms t
    | .as t i => .as t i :: subterms t
    | .app f ts => .app f ts :: subtermsList ts
    termination_by structural t => t
  def subtermsList : List Term → List Term
    | [] => []
    | t :: ts => subterms t ++ subtermsList ts
    termination_by structural ts => ts
end

theorem self_mem_subterms : ∀ (t : Term), t ∈ subterms t
  | .var _ => List.mem_singleton_self _
  | .dv _ _ => List.mem_singleton_self _
  | .inj _ _ _ => List.mem_cons_self ..
  | .as _ _ => List.mem_cons_self ..
  | .app _ _ => List.mem_cons_self ..

mutual
  theorem subterms_trans {X A : Term} : ∀ {t : Term}, A ∈ subterms t → X ∈ subterms A → X ∈ subterms t
    | .var i, hA, hX => by simp only [subterms, List.mem_singleton] at hA; subst hA; exact hX
    | .dv s l, hA, hX => by simp only [subterms, List.mem_singleton] at hA; subst hA; exact hX
    | .inj a b t, hA, hX => by
      simp only [subterms, List.mem_cons] at hA ⊢
      rcases hA with rfl | hA
      · simpa [subterms] using hX
      · exact .inr (subterms_trans hA hX)
    | .as t i, hA, hX => by
      simp only [subterms, List.mem_cons] at hA ⊢
      rcases hA with rfl | hA
      · simpa [subterms] using hX
      · exact .inr (subterms_trans hA hX)
    | .app f ts, hA, hX => by
      simp only [subterms, List.mem_cons] at hA ⊢
      rcases hA with rfl | hA
      · simpa [subterms] using hX
      · exact .inr (subtermsList_trans hA hX)
    termination_by structural t => t
  theorem subtermsList_trans {X A : Term} : ∀ {ts : List Term}, A ∈ subtermsList ts → X ∈ subterms A →
      X ∈ subtermsList ts
    | [], hA, _ => by simp [subtermsList] at hA
    | t :: ts, hA, hX => by
      simp only [subtermsList, List.mem_append] at hA ⊢
      rcases hA with hA | hA
      · exact .inl (subterms_trans hA hX)
      · exact .inr (subtermsList_trans hA hX)
    termination_by structural ts => ts
end

mutual
  /-- The variables of a term inside t are t's. -/
  theorem varOccs_subterms {X : Term} : ∀ {t : Term}, X ∈ subterms t → ∀ i ∈ varOccs X, i ∈ varOccs t
    | .var j, h, i, hi => by simp only [subterms, List.mem_singleton] at h; subst h; exact hi
    | .dv s l, h, i, hi => by simp only [subterms, List.mem_singleton] at h; subst h; exact hi
    | .inj a b t, h, i, hi => by
      simp only [subterms, List.mem_cons] at h
      rcases h with rfl | h
      · exact hi
      · simpa [varOccs] using varOccs_subterms h i hi
    | .as t j, h, i, hi => by
      simp only [subterms, List.mem_cons] at h
      rcases h with rfl | h
      · exact hi
      · simp only [varOccs, List.mem_append]; exact .inl (varOccs_subterms h i hi)
    | .app f ts, h, i, hi => by
      simp only [subterms, List.mem_cons] at h
      rcases h with rfl | h
      · exact hi
      · simpa [varOccs] using varOccsList_subterms h i hi
    termination_by structural t => t
  theorem varOccsList_subterms {X : Term} : ∀ {ts : List Term}, X ∈ subtermsList ts →
      ∀ i ∈ varOccs X, i ∈ varOccsList ts
    | [], h, _, _ => by simp [subtermsList] at h
    | t :: ts, h, i, hi => by
      simp only [subtermsList, List.mem_append] at h
      simp only [varOccsList, List.mem_append]
      rcases h with h | h
      · exact .inl (varOccs_subterms h i hi)
      · exact .inr (varOccsList_subterms h i hi)
    termination_by structural ts => ts
end

/-- `u` has one result under σ. -/
def Fun (c : Semantics) (σ : Subst) (u : Term) : Prop :=
  ∀ r r', EvalTerm c σ u r → EvalTerm c σ u r' → r = r'

/-- One result is a property of the values of a term's variables. -/
theorem Fun.congr {c : Semantics} {σ σ' : Subst} {u : Term}
    (ha : ∀ i ∈ varOccs u, σ.lookup i = σ'.lookup i) (h : Fun c σ' u) : Fun c σ u :=
  fun r r' h1 h2 => h r r' (EvalTerm.congr h1 ha) (EvalTerm.congr h2 ha)

/-- Every term inside `t` has one result under σ. -/
def HDet (c : Semantics) (σ : Subst) (t : Term) : Prop := ∀ u ∈ subterms t, Fun c σ u

/-- The clause decides at `vs` under σ, as a clause of `fn`, in the form the model reads: it applies
there under σ, and no clause of `fn` of a smaller priority that is not `aside` has its patterns
match, its `requires` evaluate to `true` and its predicate true there, under any substitution well
sorted on the variables of its patterns and conditions. -/
def Clause.DecidesAt (c : Semantics) (fn : Fn) (cl : Clause) (σ : Subst) (vs : List GroundTerm) : Prop :=
  cl.AppliesAt c σ vs ∧
    ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats vs →
        ¬ ((∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true))) ∧
           Holds c cl'.vars.length σ' cl'.pre true)

/-- The clause decides at `vs` under σ, as a clause of `fn`, as `Eval.clause` reads it: it applies
there under σ, and every clause of `fn` of a smaller priority that is not `aside` fails there. -/
def Clause.Decides (c : Semantics) (fn : Fn) (cl : Clause) (σ : Subst) (vs : List GroundTerm) : Prop :=
  cl.AppliesAt c σ vs ∧ ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl'

/-- The instance of the clause's right side at σ gives the value `v`: its right-hand side has the
value `v`, its `ensures` evaluates to `true` (or it has none), and its predicate `post` is true. -/
def Clause.Gives (c : Semantics) (cl : Clause) (σ : Subst) (v : GroundTerm) : Prop :=
  EvalTerm c σ cl.rhs (some v) ∧ (∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) ∧
    Holds c cl.vars.length σ cl.post true

/-- A result of a clause with existential variables at the match σ, the instances being at the
well-sorted σ' that are σ off the existential variables the left side does not hold: the value an
instance gives, where every instance is decided and gives it or nothing; or none, where an instance
exists and every instance is decided and gives nothing. -/
def Clause.ResEx (c : Semantics) (cl : Clause) (σ : Subst) (r : Option GroundTerm) : Prop :=
  (∃ σ' v, AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v ∧
      (∀ σ'', AgreeOff cl.exsFree σ σ'' → c.WellSorted cl.vars σ'' → InstIs c σ'' cl (some v)) ∧
      r = some v) ∨
  (r = none ∧ (∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ') ∧
      ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl none)

/-- A result of the clause at the match σ. Without existential variables: its right-hand side's
where its `ensures` evaluates to `true` (or it has none) and its predicate `post` is true, and none
where its `ensures` has another result. With existential variables: `Clause.ResEx`. -/
def Clause.Res (c : Semantics) (cl : Clause) (σ : Subst) (r : Option GroundTerm) : Prop :=
  (cl.exs = [] ∧ (((∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) ∧
        Holds c cl.vars.length σ cl.post true ∧ EvalTerm c σ cl.rhs r) ∨
      ∃ t w, cl.ens = some t ∧ EvalTerm c σ t w ∧ w ≠ some (bool true) ∧ r = none)) ∨
  (cl.exs ≠ [] ∧ cl.ResEx c σ r)

/-- The instance of the clause's right side at σ is decided, by a predicate with one truth value
and by terms with one result: its `ensures` has a result other than `true` and its terms have one
result; or its predicate `post` is false; or its right-hand side has no value and its terms have
one result; or it gives a value, the terms of its right-hand side and `ensures` having one result.
A derivation of `InstIs` for the instance holds one of the four. -/
def InstDet (c : Semantics) (cl : Clause) (σ : Subst) : Prop :=
  (∃ b, Holds c cl.vars.length σ cl.post b ∧ ∀ b', Holds c cl.vars.length σ cl.post b' → b = b') ∧
  ((∃ t w, cl.ens = some t ∧ EvalTerm c σ t w ∧ w ≠ some (bool true) ∧ HDet c σ t) ∨
   Holds c cl.vars.length σ cl.post false ∨
   (EvalTerm c σ cl.rhs none ∧ HDet c σ cl.rhs) ∨
   (∃ v, EvalTerm c σ cl.rhs (some v) ∧ HDet c σ cl.rhs ∧
      (∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) ∧ HDet c σ t) ∧
      Holds c cl.vars.length σ cl.post true))

/-- Two clauses (or one clause twice) are coherent: where both decide at one argument list, as
clauses of one function, they are without existential variables and the same instance of one
right-hand side and one `ensures`, or the two clauses have the same result at their matches
(`Clause.Res`). The one who shows it may use that the terms of the first clause's `requires` each
have one result under its match; for a first clause without existential variables, that those of
its `ensures` do, and those of its right-hand side where its `ensures` is `true`; and for one with
existential variables, that each of its instances at the match is decided by terms with one result
(`InstDet`). -/
def Coherent (c : Semantics) (cl cl' : Clause) : Prop :=
  ∀ vs σ σ', cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs →
    (∀ t, cl.req = some t → HDet c σ t) →
    (cl.exs = [] → (∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) → HDet c σ cl.rhs) →
    (cl.exs = [] → ∀ t, cl.ens = some t → HDet c σ t) →
    (cl.exs ≠ [] → ∀ σ₁, AgreeOff cl.exsFree σ σ₁ → c.WellSorted cl.vars σ₁ → InstDet c cl σ₁) →
    (∃ f fn, c.lookupFn f = some fn ∧ cl ∈ fn.clauses ∧ cl' ∈ fn.clauses ∧
      cl.Decides c fn σ vs ∧ cl'.Decides c fn σ' vs) →
    (cl.exs = [] ∧ cl'.exs = [] ∧
      cl.rhs = cl'.rhs ∧ cl.ens = cl'.ens ∧ (∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∧
      ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) ∨
    ∀ r r', cl.Res c σ r → cl'.Res c σ' r' → r = r'

/-- `Coherent` for two clauses without existential variables whose right sides' predicates are
`\top` (`coherent_iff_noExs`): where both decide at one argument list, as clauses of one function,
they are the same instance of one right-hand side and one `ensures`, or the two instances have the
same result. An instance's result is its right-hand side's where its `ensures` evaluates to `true`
(or it has none), and none where its `ensures` has another result. -/
def CoherentPlain (c : Semantics) (cl cl' : Clause) : Prop :=
  ∀ vs σ σ', cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs →
    (∀ t, cl.req = some t → HDet c σ t) →
    ((∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) → HDet c σ cl.rhs) →
    (∀ t, cl.ens = some t → HDet c σ t) →
    (∃ f fn, c.lookupFn f = some fn ∧ cl ∈ fn.clauses ∧ cl' ∈ fn.clauses ∧
      cl.Decides c fn σ vs ∧ cl'.Decides c fn σ' vs) →
    (cl.rhs = cl'.rhs ∧ cl.ens = cl'.ens ∧ (∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∧
      ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) ∨
    ∀ r r',
      ((∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) ∧ EvalTerm c σ cl.rhs r ∨
        ∃ t w, cl.ens = some t ∧ EvalTerm c σ t w ∧ w ≠ some (bool true) ∧ r = none) →
      ((∀ t, cl'.ens = some t → EvalTerm c σ' t (some (bool true))) ∧ EvalTerm c σ' cl'.rhs r' ∨
        ∃ t w, cl'.ens = some t ∧ EvalTerm c σ' t w ∧ w ≠ some (bool true) ∧ r' = none) →
      r = r'

/-- Without existential variables, a result of the clause at σ is one of the two cases: the
right-hand side's where the `ensures` is `true` and `post` is true, none where the `ensures` has
another result. -/
theorem Clause.res_noExs {c : Semantics} {cl : Clause} {σ : Subst} {r : Option GroundTerm} (h : cl.exs = []) :
    cl.Res c σ r ↔
      ((∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) ∧
        Holds c cl.vars.length σ cl.post true ∧ EvalTerm c σ cl.rhs r) ∨
        ∃ t w, cl.ens = some t ∧ EvalTerm c σ t w ∧ w ≠ some (bool true) ∧ r = none :=
  ⟨fun hr => hr.elim (fun h' => h'.2) (fun h' => absurd h h'.1), fun hr => .inl ⟨h, hr⟩⟩

/-- Two clauses without existential variables are coherent where they are as `CoherentPlain`
says: a result of such a clause is one of `CoherentPlain`'s two cases. -/
theorem Coherent.of_plain {c : Semantics} {cl cl' : Clause} (h : cl.exs = []) (h' : cl'.exs = [])
    (hc : CoherentPlain c cl cl') : Coherent c cl cl' := by
  intro vs σ σ' ha ha' hq hr he _ hd
  rcases hc vs σ σ' ha ha' hq (hr h) (he h) hd with ⟨h1, h2, h3, h4⟩ | hres
  · exact .inl ⟨h, h', h1, h2, h3, h4⟩
  · refine .inr fun r r' hr1 hr2 => hres r r' ?_ ?_
    · rcases (Clause.res_noExs h).mp hr1 with ⟨a, -, b⟩ | hx
      · exact .inl ⟨a, b⟩
      · exact .inr hx
    · rcases (Clause.res_noExs h').mp hr2 with ⟨a, -, b⟩ | hx
      · exact .inl ⟨a, b⟩
      · exact .inr hx

/-- **For two clauses without existential variables whose right sides' predicates are `\top`,
`Coherent` is the proposition without them** (`CoherentPlain`). -/
theorem coherent_iff_noExs {c : Semantics} {cl cl' : Clause} (h : cl.exs = []) (h' : cl'.exs = [])
    (hp : cl.post = .top) (hp' : cl'.post = .top) : Coherent c cl cl' ↔ CoherentPlain c cl cl' := by
  refine ⟨fun hc vs σ σ' ha ha' hq hr he hd => ?_, Coherent.of_plain h h'⟩
  rcases hc vs σ σ' ha ha' hq (fun _ => hr) (fun _ => he) (fun hne => absurd h hne) hd with
    ⟨-, -, h1, h2, h3, h4⟩ | hres
  · exact .inl ⟨h1, h2, h3, h4⟩
  · refine .inr fun r r' hr1 hr2 => hres r r' ((Clause.res_noExs h).mpr ?_) ((Clause.res_noExs h').mpr ?_)
    · rcases hr1 with ⟨a, b⟩ | hx
      · exact .inl ⟨a, by rw [hp]; exact .top, b⟩
      · exact .inr hx
    · rcases hr2 with ⟨a, b⟩ | hx
      · exact .inl ⟨a, by rw [hp']; exact .top, b⟩
      · exact .inr hx

/-- Two clauses without an `ensures` are as `CoherentPlain` says where, wherever both decide, they
are the same instance of one right-hand side or their right-hand sides have one result. -/
theorem CoherentPlain.of_rhs {c : Semantics} {cl cl' : Clause} (hn : cl.ens = none) (hn' : cl'.ens = none)
    (h : ∀ vs σ σ', cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs →
      (∀ t, cl.req = some t → HDet c σ t) → HDet c σ cl.rhs →
      (∃ f fn, c.lookupFn f = some fn ∧ cl ∈ fn.clauses ∧ cl' ∈ fn.clauses ∧
        cl.Decides c fn σ vs ∧ cl'.Decides c fn σ' vs) →
      (cl.rhs = cl'.rhs ∧ ∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∨
      ∀ r r', EvalTerm c σ cl.rhs r → EvalTerm c σ' cl'.rhs r' → r = r') : CoherentPlain c cl cl' := by
  intro vs σ σ' ha ha' hq hr _ hd
  rcases h vs σ σ' ha ha' hq (hr fun t ht => by rw [hn] at ht; cases ht) hd with ⟨he, hv⟩ | hres
  · exact .inl ⟨he, hn.trans hn'.symm, hv, fun t ht => by rw [hn] at ht; cases ht⟩
  · refine .inr fun r r' h1 h2 => ?_
    rcases h1 with ⟨-, h1⟩ | ⟨t, -, ht, -⟩
    · rcases h2 with ⟨-, h2⟩ | ⟨t, -, ht, -⟩
      · exact hres r r' h1 h2
      · rw [hn'] at ht; cases ht
    · rw [hn] at ht; cases ht

/-- Two clauses without an `ensures` or an existential variable (by default shown for clauses whose
text has none) are coherent where, wherever both decide, they are the same instance of one
right-hand side or their right-hand sides have one result: `Coherent` for them. -/
theorem Coherent.of_rhs {c : Semantics} {cl cl' : Clause} (hn : cl.ens = none) (hn' : cl'.ens = none)
    (h : ∀ vs σ σ', cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs →
      (∀ t, cl.req = some t → HDet c σ t) → HDet c σ cl.rhs →
      (∃ f fn, c.lookupFn f = some fn ∧ cl ∈ fn.clauses ∧ cl' ∈ fn.clauses ∧
        cl.Decides c fn σ vs ∧ cl'.Decides c fn σ' vs) →
      (cl.rhs = cl'.rhs ∧ ∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∨
      ∀ r r', EvalTerm c σ cl.rhs r → EvalTerm c σ' cl'.rhs r' → r = r')
    (hx : cl.exs = [] := by rfl) (hx' : cl'.exs = [] := by rfl) : Coherent c cl cl' := by
  intro vs σ σ' ha ha' hq hr _ _ hd
  rcases h vs σ σ' ha ha' hq (hr hx fun t ht => by rw [hn] at ht; cases ht) hd with ⟨he, hv⟩ | hres
  · exact .inl ⟨hx, hx', he, hn.trans hn'.symm, hv, fun t ht => by rw [hn] at ht; cases ht⟩
  · refine .inr fun r r' h1 h2 => ?_
    rcases (Clause.res_noExs hx).mp h1 with ⟨-, -, h1⟩ | ⟨t, -, ht, -⟩
    · rcases (Clause.res_noExs hx').mp h2 with ⟨-, -, h2⟩ | ⟨t, -, ht, -⟩
      · exact hres r r' h1 h2
      · rw [hn'] at ht; cases ht
    · rw [hn] at ht; cases ht

/-- Every two clauses of every function that compete are coherent, each clause with itself among
them: two of one priority, or two of which the one of the smaller priority is `aside`, which no
clause's priority premise reads. -/
def CoherentAll (c : Semantics) : Prop :=
  ∀ f fn, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, ∀ cl' ∈ fn.clauses,
    (cl.prio = cl'.prio ∨ (cl.aside = true ∧ cl.prio < cl'.prio) ∨
      (cl'.aside = true ∧ cl'.prio < cl.prio)) →
    Coherent c cl cl'

/-- The clause's result at an argument list does not depend on the match: two matches of it there
give one result, and where it has existential variables, at each match where it decides its
instances are decided and give one result (a result of the clause exists there). -/
def MatchIndependent (c : Semantics) (cl : Clause) : Prop :=
  Coherent c cl cl ∧
  (cl.exs ≠ [] → ∀ f fn vs σ, c.lookupFn f = some fn → cl ∈ fn.clauses →
    cl.Decides c fn σ vs → ∃ r, cl.Res c σ r)

/-- Without existential variables, match independence is the clause's coherence with itself. -/
theorem matchIndependent_iff_noExs {c : Semantics} {cl : Clause} (h : cl.exs = []) :
    MatchIndependent c cl ↔ Coherent c cl cl :=
  ⟨fun hm => hm.1, fun hc => ⟨hc, fun hne => absurd h hne⟩⟩

/-- Every clause of every function is match independent. -/
def MatchIndependentAll (c : Semantics) : Prop :=
  ∀ f fn, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, MatchIndependent c cl

/-- A function has at most one result at each argument list. -/
def FnDet (c : Semantics) : Prop :=
  ∀ f vs r r', Eval c f vs r → Eval c f vs r' → r = r'

/-- **Evaluation solves the equations**: where a clause decides under σ at argument values of its
function's sorts, the values of the function there are the values the instances of that clause's
right side give (`Clause.Gives`: the right-hand side's value where the `ensures` evaluates to `true`
and the predicate `post` is true), the instances being at the well-sorted σ' that are σ off the
existential variables the left side does not hold. -/
def FnSolves (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∀ cl ∈ fn.clauses, ∀ σ,
    cl.DecidesAt c fn σ vs → ∀ v, Eval c fn.label vs (some v) ↔
      ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v

/-- Without existential variables and with the right side's predicate `\top`, the instances of a
clause's right side at a well-sorted σ that give `v` are the one at σ: its right-hand side has the
value `v` and its `ensures` evaluates to `true`. -/
theorem Clause.gives_iff_noExs {c : Semantics} {cl : Clause} (hex : cl.exs = []) (hpost : cl.post = .top)
    {σ : Subst} (hσ : c.WellSorted cl.vars σ) (v : GroundTerm) :
    (∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v) ↔
      EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) := by
  have hf : cl.exsFree = [] := Clause.exsFree_nil hex
  constructor
  · rintro ⟨σ', ha, -, hr, he, -⟩
    rw [hf] at ha
    exact ⟨EvalTerm.congr hr fun i _ => ha i List.not_mem_nil,
      fun t ht => EvalTerm.congr (he t ht) fun i _ => ha i List.not_mem_nil⟩
  · rintro ⟨hr, he⟩
    exact ⟨σ, AgreeOff.refl _ _, hσ, hr, he, by rw [hpost]; exact .top⟩

/-- Where no clause of a function of the definition has an existential variable and every right
side's predicate is `\top`, `FnSolves` says that where a clause decides, the values of the function
are the values of that clause's right-hand side where its `ensures` evaluates to `true`. -/
theorem fnSolves_iff_noExs {c : Semantics}
    (hx : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top) :
    FnSolves c ↔
      ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∀ cl ∈ fn.clauses, ∀ σ,
        cl.DecidesAt c fn σ vs → ∀ v, Eval c fn.label vs (some v) ↔
          EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) :=
  ⟨fun h fn hfn vs hvs cl hcl σ hdec v => (h fn hfn vs hvs cl hcl σ hdec v).trans
      (Clause.gives_iff_noExs (hx fn hfn cl hcl).1 (hx fn hfn cl hcl).2 hdec.1.1 v),
    fun h fn hfn vs hvs cl hcl σ hdec v => (h fn hfn vs hvs cl hcl σ hdec v).trans
      (Clause.gives_iff_noExs (hx fn hfn cl hcl).1 (hx fn hfn cl hcl).2 hdec.1.1 v).symm⟩

end KCore
