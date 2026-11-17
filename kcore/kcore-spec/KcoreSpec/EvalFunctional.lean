/-
  KCore. Evaluation has one result where clauses of one priority are coherent.

  `Eval` reads no order among the clauses of one priority, so it is not functional by construction:
  two clauses of one priority, or two matches of one clause, may both apply at an argument list.
  Clauses of different priorities never compete (the larger one's derivation has the smaller one
  failing, and a clause that applies does not fail). `Coherent` says that two clauses of one
  priority give one result where both decide (both apply, and no clause of a smaller priority
  applies, `Clause.DecidesAt`); with every such pair coherent (`CoherentAll`) and no clause holding
  an existential variable (`Semantics.FnsNoExs`), a function has one result at each argument list
  (`Eval.functional`, `fnDet_of_coherent`). No sorting hypothesis is needed. Where every function
  has one result (`FnDet`), so does every term (`EvalTerm.functional_of_fnDet`).

  A clause with existential variables has its results by `Eval.clauseEx` and `Eval.exNone`
  (`Clause.Res`). A derivation by `Eval.exNone` holds no derivation for the clause's right-hand
  side or `ensures` (an instance that fails by its predicate evaluates neither), so the induction
  has nothing to give `Coherent` for them there: that is where `FnsNoExs` is read.

  The shape of `Coherent` is what the proof, an induction on the first derivation, has in hand:
  - the same instance of one right-hand side and one `ensures` (first alternative) is what a
    syntactic check shows; the induction hypotheses for the first clause's right-hand side and
    `ensures` turn it into one result;
  - one result of the two clauses at their matches (second alternative, `Clause.Res`: without
    existential variables the right-hand side's where the `ensures` is `true` and the right side's
    predicate holds, none where the `ensures` is something else) is the semantic statement, for a
    pair no check confirms; it is asked only where both clauses decide, since each `Eval`
    derivation by a clause has every clause of a smaller priority failing;
  - every term inside the first clause's `requires` and `ensures` has one result under its match,
    and so does every term inside its right-hand side where its `ensures` is `true` (`HDet`):
    evaluation is strict, so the first derivation holds a derivation for each of them, and the
    induction hypothesis covers them. Nothing is available for the second clause's terms.

  `MatchIndependent` (a clause against itself) and `ClausesAgree` (two clauses of one function)
  are its instances, the obligations `Obligations` names (Statements.lean).
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

/-- Two clauses (or one clause twice) are coherent: where both decide at one argument list, as
clauses of one function, they are without existential variables and the same instance of one
right-hand side and one `ensures`, or the two clauses have the same result at their matches
(`Clause.Res`). The one who shows it may use that the terms of the first clause's `requires` and
`ensures` each have one result under its match, and those of its right-hand side where its
`ensures` is `true`. -/
def Coherent (c : Semantics) (cl cl' : Clause) : Prop :=
  ∀ vs σ σ', cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs →
    (∀ t, cl.req = some t → HDet c σ t) →
    ((∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) → HDet c σ cl.rhs) →
    (∀ t, cl.ens = some t → HDet c σ t) →
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
  intro vs σ σ' ha ha' hq hr he hd
  rcases hc vs σ σ' ha ha' hq hr he hd with ⟨h1, h2, h3, h4⟩ | hres
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
  rcases hc vs σ σ' ha ha' hq hr he hd with ⟨-, -, h1, h2, h3, h4⟩ | hres
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
  intro vs σ σ' ha ha' hq hr _ hd
  rcases h vs σ σ' ha ha' hq (hr fun t ht => by rw [hn] at ht; cases ht) hd with ⟨he, hv⟩ | hres
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

/-- Two clauses that compete and both decide at `vs`, as `Eval`'s constructors read deciding, the
first under σ with the induction hypotheses of its derivation: the coherence of the pair, and the
hypotheses it asks. -/
theorem coh_of {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl cl' : Clause} {σ σ' : Subst}
    (hco : CoherentAll c) (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hmem' : cl' ∈ fn.clauses)
    (hcomp : cl.prio = cl'.prio ∨ (cl.aside = true ∧ cl.prio < cl'.prio) ∨
      (cl'.aside = true ∧ cl'.prio < cl.prio))
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hprio : ∀ cl'' ∈ fn.clauses, cl''.aside = false → cl''.prio < cl.prio → Fails c vs cl'')
    (hσ' : c.WellSorted cl'.vars σ') (hmatch' : PatVals c σ' cl'.pats vs)
    (hreq' : ∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true)))
    (hpre' : Holds c cl'.vars.length σ' cl'.pre true)
    (hprio' : ∀ cl'' ∈ fn.clauses, cl''.aside = false → cl''.prio < cl'.prio → Fails c vs cl'')
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (hrd : (∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) → HDet c σ cl.rhs)
    (hed : ∀ t, cl.ens = some t → HDet c σ t) :
    (cl.exs = [] ∧ cl'.exs = [] ∧
      cl.rhs = cl'.rhs ∧ cl.ens = cl'.ens ∧ (∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∧
      ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) ∨
    ∀ r r', cl.Res c σ r → cl'.Res c σ' r' → r = r' :=
  hco f fn hfn cl hmem cl' hmem' hcomp vs σ σ' ⟨hσ, hmatch, hreq, hpre⟩ ⟨hσ', hmatch', hreq', hpre'⟩
    (fun t ht => (ihreq t ht).2) hrd hed
    ⟨f, fn, hfn, hmem, hmem', ⟨⟨hσ, hmatch, hreq, hpre⟩, hprio⟩, ⟨⟨hσ', hmatch', hreq', hpre'⟩, hprio'⟩⟩

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

/-- A derivation by a clause, the first, with the induction hypotheses for its `requires`, its
predicate and the clauses of a smaller priority, against a second derivation at the same argument
list, given the first clause's result `r` at its match (`hres`) and what `Coherent` asks of its
right-hand side and `ensures` (`hrd`, `hed`): where the two clauses are the same instance
(`hsame`), or by the two results. No clause of the function has an existential variable (`hno`):
read where the second derivation is by `Eval.exNone`, whose match is well sorted on the variables
its right side does not bind only. -/
theorem case_by {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    {r : Option GroundTerm} (hco : CoherentAll c) (hno : c.FnsNoExs)
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (ihpre : M6 c cl.vars.length σ cl.pre true)
    (ihprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → M2 c vs cl')
    (hrd : (∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) → HDet c σ cl.rhs)
    (hed : ∀ t, cl.ens = some t → HDet c σ t)
    (hres : cl.Res c σ r)
    (hsame : ∀ (cl' : Clause) (σ' : Subst) (r' : Option GroundTerm), cl.exs = [] → cl'.exs = [] → cl.rhs = cl'.rhs →
      cl.ens = cl'.ens → (∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) →
      (∀ t, cl.ens = some t → ∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) →
      cl'.Res c σ' r' → r = r') : M1 c f vs r := by
  have key : ∀ (cl' : Clause) (σ' : Subst) (r' : Option GroundTerm), cl' ∈ fn.clauses →
      c.WellSorted cl'.vars σ' → PatVals c σ' cl'.pats vs →
      (∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true))) →
      Holds c cl'.vars.length σ' cl'.pre true →
      (∀ cl'' ∈ fn.clauses, cl''.aside = false → cl''.prio < cl'.prio → Fails c vs cl'') →
      cl'.Res c σ' r' → r = r' := by
    intro cl' σ' r' hmem' hσ' hmatch' hreq' hpre' hprio' hres'
    rcases compete_or_blocks cl cl' with hcomp | ⟨ha, hlt⟩ | ⟨ha, hgt⟩
    · rcases coh_of hco hfn hmem hmem' hcomp hσ hmatch hreq hpre hprio hσ' hmatch' hreq' hpre' hprio' ihreq
          hrd hed with ⟨hx, hx', he, hee, hv, hve⟩ | hr
      · exact hsame cl' σ' r' hx hx' he hee hv hve hres'
      · exact hr _ _ hres hres'
    · exact (not_fails hσ hmatch ihreq ihpre (hprio' _ hmem ha hlt)).elim
    · exact (ihprio _ hmem' ha hgt _ (hσ'.at _) hmatch' hreq' hpre').elim
  intro r' h'
  cases h' with
  | @clause _ _ _ cl' σ' _ hfn' hmem' hσ' hmatch' hreq' hpre' hprio' hex' hrhs' hens' hpost' =>
    rw [hfn] at hfn'; cases hfn'
    exact key cl' σ' r' hmem' hσ' hmatch' hreq' hpre' hprio' (.inl ⟨hex', .inl ⟨hens', hpost', hrhs'⟩⟩)
  | rest hfn' hnone' =>
    rw [hfn] at hfn'; cases hfn'
    exact (not_fails hσ hmatch ihreq ihpre (hnone' _ hmem)).elim
  | @ensFails _ _ _ cl' σ' t' w' hfn' hmem' hσ' hmatch' hreq' hpre' hprio' hex' ht' he' hw' =>
    rw [hfn] at hfn'; cases hfn'
    exact key cl' σ' none hmem' hσ' hmatch' hreq' hpre' hprio' (.inl ⟨hex', .inr ⟨t', w', ht', he', hw', rfl⟩⟩)
  | @clauseEx _ _ _ cl' σ' v' hfn' hmem' hσ' hmatch' hreq' hpre' hprio' hne' hrhs' hens' hpost' hall' =>
    rw [hfn] at hfn'; cases hfn'
    exact key cl' σ' (some v') hmem' hσ' hmatch' hreq' hpre' hprio' (res_clauseEx hσ' hne' hrhs' hens' hpost' hall')
  | @exNone _ _ _ cl' σ' hfn' hmem' hne' _ _ _ _ _ _ _ =>
    rw [hfn] at hfn'; cases hfn'
    exact absurd (hno.lookup hfn hmem') hne'

theorem case_clause (hco : CoherentAll c) (hno : c.FnsNoExs) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    {cl : Clause} {σ : Subst} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
    (hex : cl.exs = [])
    (hrhs : EvalTerm c σ cl.rhs r)
    (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c cl.vars.length σ cl.post true)
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (ihpre : M6 c cl.vars.length σ cl.pre true)
    (ihprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → M2 c vs cl')
    (ihrhs : M4 c σ cl.rhs r)
    (ihens : ∀ t, cl.ens = some t → M4 c σ t (some (bool true))) : M1 c f vs r :=
  case_by hco hno hfn hmem hσ hmatch hreq hpre hprio ihreq ihpre ihprio (fun _ => ihrhs.2)
    (fun t ht => (ihens t ht).2) (.inl ⟨hex, .inl ⟨hens, hpost, hrhs⟩⟩)
    fun cl' σ' r' _ hx' he hee hv hve hres' => by
      rcases (Clause.res_noExs hx').mp hres' with ⟨-, -, hrhs'⟩ | ⟨t', w', ht', he', hw', rfl⟩
      · rw [← he] at hrhs'
        exact ihrhs.1 r' (EvalTerm.congr hrhs' fun i hi => (hv i hi).symm)
      · rw [← hee] at ht'
        exact (hw' ((ihens t' ht').1 w' (EvalTerm.congr he' fun i hi => (hve t' ht' i hi).symm)).symm).elim

theorem case_ensFails (hco : CoherentAll c) (hno : c.FnsNoExs) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    {cl : Clause} {σ : Subst} {t : Term} {w : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
    (hex : cl.exs = [])
    (ht : cl.ens = some t) (he : EvalTerm c σ t w) (hw : w ≠ some (bool true))
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (ihpre : M6 c cl.vars.length σ cl.pre true)
    (ihprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → M2 c vs cl')
    (ihe : M4 c σ t w) : M1 c f vs none := by
  have hnot : ¬ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) :=
    fun h => hw (ihe.1 _ (h t ht))
  have hed : ∀ t', cl.ens = some t' → HDet c σ t' := fun t' ht'' => by
    rw [ht] at ht''; cases ht''; exact ihe.2
  exact case_by hco hno hfn hmem hσ hmatch hreq hpre hprio ihreq ihpre ihprio (fun h => (hnot h).elim) hed
    (.inl ⟨hex, .inr ⟨t, w, ht, he, hw, rfl⟩⟩)
    fun cl' σ' r' _ hx' _ hee _ hve hres' => by
      rcases (Clause.res_noExs hx').mp hres' with ⟨hens', -, -⟩ | ⟨_, _, _, _, _, rfl⟩
      · exact (hnot fun t'' ht'' =>
          EvalTerm.congr (hens' t'' (hee ▸ ht'')) fun i hi => (hve t'' ht'' i hi).symm).elim
      · rfl

/-- A derivation by `Eval.clauseEx`: its match is an instance that gives the value, so the terms of
its right-hand side and `ensures` have one result there, and its result is a result of its clause
at its match. -/
theorem case_clauseEx (hco : CoherentAll c) (hno : c.FnsNoExs) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    {cl : Clause} {σ : Subst} {v : GroundTerm}
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
    (hne : cl.exs ≠ [])
    (hrhs : EvalTerm c σ cl.rhs (some v))
    (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c cl.vars.length σ cl.post true)
    (hall : ∀ σ', AgreeOff cl.exsFree σ σ' → c.WellSorted cl.vars σ' → InstIs c σ' cl (some v))
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (ihpre : M6 c cl.vars.length σ cl.pre true)
    (ihprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → M2 c vs cl')
    (ihrhs : M4 c σ cl.rhs (some v))
    (ihens : ∀ t, cl.ens = some t → M4 c σ t (some (bool true))) : M1 c f vs (some v) :=
  case_by hco hno hfn hmem hσ hmatch hreq hpre hprio ihreq ihpre ihprio (fun _ => ihrhs.2)
    (fun t ht => (ihens t ht).2) (res_clauseEx hσ hne hrhs hens hpost hall)
    fun _ _ _ hx _ _ _ _ _ _ => absurd hx hne

/-- A derivation by `Eval.exNone` holds no derivation for its clause's right-hand side or
`ensures`: where no clause has an existential variable there is none. -/
theorem case_exNone (hno : c.FnsNoExs) {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause}
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses) (hne : cl.exs ≠ []) : M1 c f vs none :=
  absurd (hno.lookup hfn hmem) hne

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
/-- **A function has one result at each argument list** when clauses of one priority are
coherent and no clause has an existential variable. -/
theorem Eval.functional {c : Semantics} (hco : CoherentAll c) (hno : c.FnsNoExs) {f : Sym}
    {vs : List GroundTerm} {r r' : Option GroundTerm} (h : Eval c f vs r) (h' : Eval c f vs r') :
    r = r' :=
  Eval.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun n σ p b _ => M6 c n σ p b)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost ihreq ihpre ihprio ihrhs ihens _ =>
      case_clause hco hno hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost ihreq ihpre ihprio ihrhs ihens)
    (fun hfn _ ihnone => case_rest hfn ihnone)
    (fun hfn hmem hσ hmatch hreq hpre hprio hex ht he hw ihreq ihpre ihprio ihe =>
      case_ensFails hco hno hfn hmem hσ hmatch hreq hpre hprio hex ht he hw ihreq ihpre ihprio ihe)
    (fun hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall ihreq ihpre ihprio ihrhs ihens _ _ =>
      case_clauseEx hco hno hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall ihreq ihpre ihprio
        ihrhs ihens)
    (fun hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => case_exNone hno hfn hmem hne)
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
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    h r' h'

open EvalFunctional in
/-- A term has one result under each substitution when clauses of one priority are coherent and no
clause has an existential variable; so does every term inside it. -/
theorem EvalTerm.functional_hdet {c : Semantics} (hco : CoherentAll c) (hno : c.FnsNoExs) {σ : Subst} {t : Term}
    {r : Option GroundTerm} (h : EvalTerm c σ t r) : (∀ r', EvalTerm c σ t r' → r = r') ∧ HDet c σ t :=
  EvalTerm.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun n σ p b _ => M6 c n σ p b)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost ihreq ihpre ihprio ihrhs ihens _ =>
      case_clause hco hno hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost ihreq ihpre ihprio ihrhs ihens)
    (fun hfn _ ihnone => case_rest hfn ihnone)
    (fun hfn hmem hσ hmatch hreq hpre hprio hex ht he hw ihreq ihpre ihprio ihe =>
      case_ensFails hco hno hfn hmem hσ hmatch hreq hpre hprio hex ht he hw ihreq ihpre ihprio ihe)
    (fun hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall ihreq ihpre ihprio ihrhs ihens _ _ =>
      case_clauseEx hco hno hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall ihreq ihpre ihprio
        ihrhs ihens)
    (fun hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => case_exNone hno hfn hmem hne)
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
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    h

/-- A term has one result under each substitution when clauses of one priority are coherent and no
clause has an existential variable. -/
theorem EvalTerm.functional {c : Semantics} (hco : CoherentAll c) (hno : c.FnsNoExs) {σ : Subst} {t : Term}
    {r r' : Option GroundTerm} (h : EvalTerm c σ t r) (h' : EvalTerm c σ t r') : r = r' :=
  (EvalTerm.functional_hdet hco hno h).1 r' h'

open EvalFunctional in
/-- A condition has one truth value under each substitution when clauses of one priority are
coherent and no clause has an existential variable. -/
theorem Holds.functional {c : Semantics} (hco : CoherentAll c) (hno : c.FnsNoExs) {n : Nat} {σ : Subst} {p : Cond}
    {b b' : Bool} (h : Holds c n σ p b) (h' : Holds c n σ p b') : b = b' :=
  Holds.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun n σ p b _ => M6 c n σ p b)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost ihreq ihpre ihprio ihrhs ihens _ =>
      case_clause hco hno hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost ihreq ihpre ihprio ihrhs ihens)
    (fun hfn _ ihnone => case_rest hfn ihnone)
    (fun hfn hmem hσ hmatch hreq hpre hprio hex ht he hw ihreq ihpre ihprio ihe =>
      case_ensFails hco hno hfn hmem hσ hmatch hreq hpre hprio hex ht he hw ihreq ihpre ihprio ihe)
    (fun hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall ihreq ihpre ihprio ihrhs ihens _ _ =>
      case_clauseEx hco hno hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost hall ihreq ihpre ihprio
        ihrhs ihens)
    (fun hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => case_exNone hno hfn hmem hne)
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
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    h b' h'

/-- A function has at most one result at each argument list. -/
def FnDet (c : Semantics) : Prop :=
  ∀ f vs r r', Eval c f vs r → Eval c f vs r' → r = r'

/-- **Evaluation solves the equations**: where a clause decides at argument values of its
function's sorts, the values of the function there are the values of that clause's right-hand
side where its `ensures` evaluates to `true`. -/
def FnSolves (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∀ cl ∈ fn.clauses, ∀ σ,
    cl.DecidesAt c fn σ vs → ∀ v, Eval c fn.label vs (some v) ↔
      EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))

/-- Clauses that compete coherent and none with an existential variable, every function has at most
one result. -/
theorem fnDet_of_coherent {c : Semantics} (hco : CoherentAll c) (hno : c.FnsNoExs) : FnDet c :=
  fun _ _ _ _ h h' => Eval.functional hco hno h h'

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

end KCore
