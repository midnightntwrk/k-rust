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
  (`EvalTerm.functional_of_fnDet`).

  The shape of `Coherent` is what the proof, an induction on the first derivation, has in hand:
  - the same instance of one right-hand side and one `ensures` (first alternative) is what a
    syntactic check shows; the induction hypotheses for the first clause's right-hand side and
    `ensures` turn it into one result;
  - one result of the two instances (second alternative: the right-hand side's where the `ensures`
    is `true`, none where it is something else) is the semantic statement, for a pair no check
    confirms; it is asked only where both clauses decide, since each `Eval.clause` and
    `Eval.ensFails` derivation has every clause of a smaller priority failing;
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

/-- The clause applies at `vs` under σ: σ is well sorted, the patterns denote `vs`, and the
`requires` evaluates to `true`. -/
def Clause.AppliesAt (c : Semantics) (cl : Clause) (σ : Subst) (vs : List GroundTerm) : Prop :=
  c.WellSorted cl.vars σ ∧ PatVals c σ cl.pats vs ∧
    ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))

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
match and its `requires` evaluate to `true` there, under any substitution well sorted on the
variables of its patterns and conditions. -/
def Clause.DecidesAt (c : Semantics) (fn : Fn) (cl : Clause) (σ : Subst) (vs : List GroundTerm) : Prop :=
  cl.AppliesAt c σ vs ∧
    ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats vs →
        ¬ ∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true))

/-- The clause decides at `vs` under σ, as a clause of `fn`, as `Eval.clause` reads it: it applies
there under σ, and every clause of `fn` of a smaller priority that is not `aside` fails there. -/
def Clause.Decides (c : Semantics) (fn : Fn) (cl : Clause) (σ : Subst) (vs : List GroundTerm) : Prop :=
  cl.AppliesAt c σ vs ∧ ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl'

/-- Two clauses (or one clause twice) are coherent: where both decide at one argument list, as
clauses of one function, they are the same instance of one right-hand side and one `ensures`, or
the two instances have the same result. An instance's result is its right-hand side's where its
`ensures` evaluates to `true` (or it has none), and none where its `ensures` has another result.
The one who shows it may use that the terms of the first clause's `requires` and `ensures` each have
one result under its match, and those of its right-hand side where its `ensures` is `true`. -/
def Coherent (c : Semantics) (cl cl' : Clause) : Prop :=
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

/-- Two clauses without an `ensures` are coherent where, wherever both decide, they are the same
instance of one right-hand side or their right-hand sides have one result: `Coherent` for them. -/
theorem Coherent.of_rhs {c : Semantics} {cl cl' : Clause} (hn : cl.ens = none) (hn' : cl'.ens = none)
    (h : ∀ vs σ σ', cl.AppliesAt c σ vs → cl'.AppliesAt c σ' vs →
      (∀ t, cl.req = some t → HDet c σ t) → HDet c σ cl.rhs →
      (∃ f fn, c.lookupFn f = some fn ∧ cl ∈ fn.clauses ∧ cl' ∈ fn.clauses ∧
        cl.Decides c fn σ vs ∧ cl'.Decides c fn σ' vs) →
      (cl.rhs = cl'.rhs ∧ ∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∨
      ∀ r r', EvalTerm c σ cl.rhs r → EvalTerm c σ' cl'.rhs r' → r = r') : Coherent c cl cl' := by
  intro vs σ σ' ha ha' hq hr _ hd
  rcases h vs σ σ' ha ha' hq (hr fun t ht => by rw [hn] at ht; cases ht) hd with ⟨he, hv⟩ | hres
  · exact .inl ⟨he, hn.trans hn'.symm, hv, fun t ht => by rw [hn] at ht; cases ht⟩
  · refine .inr fun r r' h1 h2 => ?_
    rcases h1 with ⟨-, h1⟩ | ⟨t, -, ht, -⟩
    · rcases h2 with ⟨-, h2⟩ | ⟨t, -, ht, -⟩
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

/-- Two matches of the clause at one argument list give one result: the clause is coherent with
itself. -/
def MatchIndependent (c : Semantics) (cl : Clause) : Prop := Coherent c cl cl

/-- Every clause of every function is match independent. -/
def MatchIndependentAll (c : Semantics) : Prop :=
  ∀ f fn, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, MatchIndependent c cl

namespace EvalFunctional

variable {c : Semantics}

abbrev M1 (c : Semantics) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ r', Eval c f vs r' → r = r'
abbrev M2 (c : Semantics) (vs : List GroundTerm) (cl : Clause) : Prop :=
  ∀ σ, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs →
    (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → False
abbrev M3 (c : Semantics) (σ : Subst) (cl : Clause) : Prop :=
  (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → False
abbrev M4 (c : Semantics) (σ : Subst) (t : Term) (r : Option GroundTerm) : Prop :=
  (∀ r', EvalTerm c σ t r' → r = r') ∧ HDet c σ t
abbrev M5 (c : Semantics) (σ : Subst) (ts : List Term) (rs : List (Option GroundTerm)) : Prop :=
  (∀ rs', EvalTerms c σ ts rs' → rs = rs') ∧ ∀ u ∈ subtermsList ts, Fun c σ u

theorem mk4 {σ : Subst} {t : Term} {r : Option GroundTerm}
    (top : ∀ r', EvalTerm c σ t r' → r = r')
    (sub : ∀ u ∈ subterms t, u = t ∨ Fun c σ u) : M4 c σ t r :=
  ⟨top, fun u hu => (sub u hu).elim (fun h => h ▸ fun _ _ h1 h2 => (top _ h1).symm.trans (top _ h2)) id⟩

/-- A clause that applies under σ, its `requires` having one result there, does not fail. -/
theorem not_fails {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true))) (hf : Fails c vs cl) :
    False := by
  cases hf with
  | intro h =>
    cases h σ (hσ.at _) hmatch with
    | intro ht he hr => exact hr ((ihreq _ ht).1 _ he).symm

/-- Two clauses that compete and both decide at `vs`, as `Eval.clause` reads deciding, the first
under σ with the induction hypotheses of its derivation: the coherence of the pair, and the
hypotheses it asks. -/
theorem coh_of {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl cl' : Clause} {σ σ' : Subst}
    (hco : CoherentAll c) (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hmem' : cl' ∈ fn.clauses)
    (hcomp : cl.prio = cl'.prio ∨ (cl.aside = true ∧ cl.prio < cl'.prio) ∨
      (cl'.aside = true ∧ cl'.prio < cl.prio))
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hprio : ∀ cl'' ∈ fn.clauses, cl''.aside = false → cl''.prio < cl.prio → Fails c vs cl'')
    (hσ' : c.WellSorted cl'.vars σ') (hmatch' : PatVals c σ' cl'.pats vs)
    (hreq' : ∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true)))
    (hprio' : ∀ cl'' ∈ fn.clauses, cl''.aside = false → cl''.prio < cl'.prio → Fails c vs cl'')
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (hrd : (∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) → HDet c σ cl.rhs)
    (hed : ∀ t, cl.ens = some t → HDet c σ t) :
    (cl.rhs = cl'.rhs ∧ cl.ens = cl'.ens ∧ (∀ i ∈ varOccs cl.rhs, σ.lookup i = σ'.lookup i) ∧
      ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) ∨
    ∀ r r',
      ((∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) ∧ EvalTerm c σ cl.rhs r ∨
        ∃ t w, cl.ens = some t ∧ EvalTerm c σ t w ∧ w ≠ some (bool true) ∧ r = none) →
      ((∀ t, cl'.ens = some t → EvalTerm c σ' t (some (bool true))) ∧ EvalTerm c σ' cl'.rhs r' ∨
        ∃ t w, cl'.ens = some t ∧ EvalTerm c σ' t w ∧ w ≠ some (bool true) ∧ r' = none) →
      r = r' :=
  hco f fn hfn cl hmem cl' hmem' hcomp vs σ σ' ⟨hσ, hmatch, hreq⟩ ⟨hσ', hmatch', hreq'⟩
    (fun t ht => (ihreq t ht).2) hrd hed
    ⟨f, fn, hfn, hmem, hmem', ⟨⟨hσ, hmatch, hreq⟩, hprio⟩, ⟨⟨hσ', hmatch', hreq'⟩, hprio'⟩⟩

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

theorem case_clause (hco : CoherentAll c) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    {cl : Clause} {σ : Subst} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
    (hrhs : EvalTerm c σ cl.rhs r)
    (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)))
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (ihprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → M2 c vs cl')
    (ihrhs : M4 c σ cl.rhs r)
    (ihens : ∀ t, cl.ens = some t → M4 c σ t (some (bool true))) : M1 c f vs r := by
  intro r' h'
  cases h' with
  | @clause _ _ _ cl' σ' _ hfn' hmem' hσ' hmatch' hreq' hprio' hrhs' hens' =>
    rw [hfn] at hfn'; cases hfn'
    rcases compete_or_blocks cl cl' with hcomp | ⟨ha, hlt⟩ | ⟨ha, hgt⟩
    · rcases coh_of hco hfn hmem hmem' hcomp hσ hmatch hreq hprio hσ' hmatch' hreq' hprio' ihreq
          (fun _ => ihrhs.2) (fun t ht => (ihens t ht).2) with ⟨he, -, hv, -⟩ | hr
      · rw [← he] at hrhs'
        exact ihrhs.1 r' (EvalTerm.congr hrhs' fun i hi => (hv i hi).symm)
      · exact hr _ _ (.inl ⟨hens, hrhs⟩) (.inl ⟨hens', hrhs'⟩)
    · exact (not_fails hσ hmatch ihreq (hprio' _ hmem ha hlt)).elim
    · exact (ihprio _ hmem' ha hgt _ (hσ'.at _) hmatch' hreq').elim
  | rest hfn' hnone' =>
    rw [hfn] at hfn'; cases hfn'
    exact (not_fails hσ hmatch ihreq (hnone' _ hmem)).elim
  | @ensFails _ _ _ cl' σ' t' w' hfn' hmem' hσ' hmatch' hreq' hprio' ht' he' hw' =>
    rw [hfn] at hfn'; cases hfn'
    rcases compete_or_blocks cl cl' with hcomp | ⟨ha, hlt⟩ | ⟨ha, hgt⟩
    · rcases coh_of hco hfn hmem hmem' hcomp hσ hmatch hreq hprio hσ' hmatch' hreq' hprio' ihreq
          (fun _ => ihrhs.2) (fun t ht => (ihens t ht).2) with ⟨-, he, -, hv⟩ | hr
      · rw [← he] at ht'
        exact (hw' ((ihens t' ht').1 w' (EvalTerm.congr he' fun i hi => (hv t' ht' i hi).symm)).symm).elim
      · exact hr _ _ (.inl ⟨hens, hrhs⟩) (.inr ⟨t', w', ht', he', hw', rfl⟩)
    · exact (not_fails hσ hmatch ihreq (hprio' _ hmem ha hlt)).elim
    · exact (ihprio _ hmem' ha hgt _ (hσ'.at _) hmatch' hreq').elim

theorem case_ensFails (hco : CoherentAll c) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    {cl : Clause} {σ : Subst} {t : Term} {w : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
    (ht : cl.ens = some t) (he : EvalTerm c σ t w) (hw : w ≠ some (bool true))
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (ihprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → M2 c vs cl')
    (ihe : M4 c σ t w) : M1 c f vs none := by
  have hnot : ¬ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) :=
    fun h => hw (ihe.1 _ (h t ht))
  have hed : ∀ t', cl.ens = some t' → HDet c σ t' := fun t' ht'' => by
    rw [ht] at ht''; cases ht''; exact ihe.2
  intro r' h'
  cases h' with
  | @clause _ _ _ cl' σ' _ hfn' hmem' hσ' hmatch' hreq' hprio' hrhs' hens' =>
    rw [hfn] at hfn'; cases hfn'
    rcases compete_or_blocks cl cl' with hcomp | ⟨ha, hlt⟩ | ⟨ha, hgt⟩
    · rcases coh_of hco hfn hmem hmem' hcomp hσ hmatch hreq hprio hσ' hmatch' hreq' hprio' ihreq
          (fun h => (hnot h).elim) hed with ⟨-, hee, -, hv⟩ | hr
      · exact (hnot fun t'' ht'' =>
          EvalTerm.congr (hens' t'' (hee ▸ ht'')) fun i hi => (hv t'' ht'' i hi).symm).elim
      · exact hr _ _ (.inr ⟨t, w, ht, he, hw, rfl⟩) (.inl ⟨hens', hrhs'⟩)
    · exact (not_fails hσ hmatch ihreq (hprio' _ hmem ha hlt)).elim
    · exact (ihprio _ hmem' ha hgt _ (hσ'.at _) hmatch' hreq').elim
  | rest hfn' hnone' =>
    rw [hfn] at hfn'; cases hfn'
    exact (not_fails hσ hmatch ihreq (hnone' _ hmem)).elim
  | ensFails => rfl

theorem case_rest {f : Sym} {fn : Fn} {vs : List GroundTerm}
    (hfn : c.lookupFn f = some fn)
    (ihnone : ∀ cl ∈ fn.clauses, M2 c vs cl) : M1 c f vs (c.fnRest fn vs) := by
  intro r' h'
  cases h' with
  | clause hfn' hmem' hσ' hmatch' hreq' _ _ _ =>
    rw [hfn] at hfn'; cases hfn'
    exact (ihnone _ hmem' _ (hσ'.at _) hmatch' hreq').elim
  | rest hfn' _ => rw [hfn] at hfn'; cases hfn'; rfl
  | ensFails hfn' hmem' hσ' hmatch' hreq' _ _ _ _ =>
    rw [hfn] at hfn'; cases hfn'
    exact (ihnone _ hmem' _ (hσ'.at _) hmatch' hreq').elim

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
    | ovl h => rw [hk] at h; cases h) (sub_app ihts)

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
    | ovl _ ho => rw [(c.isOvl_parts ho).2.1] at hhk; cases hhk) (sub_app ihts)

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
    | ovl _ ho => rw [(c.isOvl_parts ho).2.2.1] at hp; cases hp) (sub_app ihts)

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
    | ovl _ ho => rw [hno] at ho; cases ho) (sub_app ihts)

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
    | ovl _ _ hts' => have := ihts.1 _ hts'; subst this; rw [hvs]; rfl) (sub_app ihts)

theorem case_ovl {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = false) (ho : c.isOvl f = true) (ihts : M5 c σ ts rs) :
    M4 c σ (.app f ts) ((allSome rs).map (c.norm f)) :=
  have hp := c.isOvl_parts ho
  mk4 (fun r' h' => by
    cases h' with
    | ctor h => rw [hk] at h; cases h
    | hook _ h => rw [hp.2.1] at h; cases h
    | param _ _ h => rw [hp.2.2.1] at h; cases h
    | call _ _ _ _ hf' _ => rw [hf'.isOvl_false] at ho; cases ho
    | callUndef _ _ hts' hvs' _ => have := ihts.1 _ hts'; subst this; rw [hvs']; rfl
    | ovl _ _ hts' => have := ihts.1 _ hts'; subst this; rfl) (sub_app ihts)

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

abbrev M6 (c : Semantics) (n : Nat) (σ : Subst) (p : Cond) (b : Bool) : Prop :=
  ∀ b', Holds c n σ p b' → b = b'

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
coherent. -/
theorem Eval.functional {c : Semantics} (hco : CoherentAll c) {f : Sym}
    {vs : List GroundTerm} {r r' : Option GroundTerm} (h : Eval c f vs r) (h' : Eval c f vs r') :
    r = r' :=
  Eval.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun n σ p b _ => M6 c n σ p b)
    (fun hfn hmem hσ hmatch hreq hprio hrhs hens ihreq ihprio ihrhs ihens =>
      case_clause hco hfn hmem hσ hmatch hreq hprio hrhs hens ihreq ihprio ihrhs ihens)
    (fun hfn _ ihnone => case_rest hfn ihnone)
    (fun hfn hmem hσ hmatch hreq hprio ht he hw ihreq ihprio ihe =>
      case_ensFails hco hfn hmem hσ hmatch hreq hprio ht he hw ihreq ihprio ihe)
    (fun _ ih => fun σ hw hp hq => ih σ hw hp hq)
    (fun ht _ hr ihe => fun hall => hr (ihe.1 _ (hall _ ht)))
    (leaf rfl fun r' h' => by cases h'; rfl)
    (leaf rfl fun r' h' => by cases h'; rfl)
    (fun _ ih => case_inj ih)
    (fun hk _ ihts => case_ctor hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hk hhk hp hr ihts)
    (fun hk hhk _ hvs hf hp ihts ihf => case_call hk hhk hvs hp hf.isOvl_false ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hk hhk hvs hp ihts)
    (fun hk ho _ ihts => case_ovl hk ho ihts)
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
    h r' h'

open EvalFunctional in
/-- A term has one result under each substitution when clauses of one priority are coherent; so
does every term inside it. -/
theorem EvalTerm.functional_hdet {c : Semantics} (hco : CoherentAll c) {σ : Subst} {t : Term}
    {r : Option GroundTerm} (h : EvalTerm c σ t r) : (∀ r', EvalTerm c σ t r' → r = r') ∧ HDet c σ t :=
  EvalTerm.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun n σ p b _ => M6 c n σ p b)
    (fun hfn hmem hσ hmatch hreq hprio hrhs hens ihreq ihprio ihrhs ihens =>
      case_clause hco hfn hmem hσ hmatch hreq hprio hrhs hens ihreq ihprio ihrhs ihens)
    (fun hfn _ ihnone => case_rest hfn ihnone)
    (fun hfn hmem hσ hmatch hreq hprio ht he hw ihreq ihprio ihe =>
      case_ensFails hco hfn hmem hσ hmatch hreq hprio ht he hw ihreq ihprio ihe)
    (fun _ ih => fun σ hw hp hq => ih σ hw hp hq)
    (fun ht _ hr ihe => fun hall => hr (ihe.1 _ (hall _ ht)))
    (leaf rfl fun r' h' => by cases h'; rfl)
    (leaf rfl fun r' h' => by cases h'; rfl)
    (fun _ ih => case_inj ih)
    (fun hk _ ihts => case_ctor hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hk hhk hp hr ihts)
    (fun hk hhk _ hvs hf hp ihts ihf => case_call hk hhk hvs hp hf.isOvl_false ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hk hhk hvs hp ihts)
    (fun hk ho _ ihts => case_ovl hk ho ihts)
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
    h

/-- A term has one result under each substitution when clauses of one priority are coherent. -/
theorem EvalTerm.functional {c : Semantics} (hco : CoherentAll c) {σ : Subst} {t : Term}
    {r r' : Option GroundTerm} (h : EvalTerm c σ t r) (h' : EvalTerm c σ t r') : r = r' :=
  (EvalTerm.functional_hdet hco h).1 r' h'

open EvalFunctional in
/-- A condition has one truth value under each substitution when clauses of one priority are
coherent. -/
theorem Holds.functional {c : Semantics} (hco : CoherentAll c) {n : Nat} {σ : Subst} {p : Cond}
    {b b' : Bool} (h : Holds c n σ p b) (h' : Holds c n σ p b') : b = b' :=
  Holds.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun n σ p b _ => M6 c n σ p b)
    (fun hfn hmem hσ hmatch hreq hprio hrhs hens ihreq ihprio ihrhs ihens =>
      case_clause hco hfn hmem hσ hmatch hreq hprio hrhs hens ihreq ihprio ihrhs ihens)
    (fun hfn _ ihnone => case_rest hfn ihnone)
    (fun hfn hmem hσ hmatch hreq hprio ht he hw ihreq ihprio ihe =>
      case_ensFails hco hfn hmem hσ hmatch hreq hprio ht he hw ihreq ihprio ihe)
    (fun _ ih => fun σ hw hp hq => ih σ hw hp hq)
    (fun ht _ hr ihe => fun hall => hr (ihe.1 _ (hall _ ht)))
    (leaf rfl fun r' h' => by cases h'; rfl)
    (leaf rfl fun r' h' => by cases h'; rfl)
    (fun _ ih => case_inj ih)
    (fun hk _ ihts => case_ctor hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hk hhk hp hr ihts)
    (fun hk hhk _ hvs hf hp ihts ihf => case_call hk hhk hvs hp hf.isOvl_false ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hk hhk hvs hp ihts)
    (fun hk ho _ ihts => case_ovl hk ho ihts)
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

/-- Clauses that compete coherent, every function has at most one result. -/
theorem fnDet_of_coherent {c : Semantics} (hco : CoherentAll c) : FnDet c :=
  fun _ _ _ _ h h' => Eval.functional hco h h'

/-- One result at each argument list gives the coherence of every two clauses: each instance's
result is an `Eval` result (`Eval.clause` or `Eval.ensFails`, the `Decides` premise as its
`hprio`), and `FnDet` equates the two. -/
theorem Coherent.of_fnDet {c : Semantics} (hd : FnDet c) (cl cl' : Clause) : Coherent c cl cl' := by
  intro vs σ σ' _ _ _ _ _ ⟨f, fn, hfn, hmem, hmem', ⟨⟨hσ, hm, hq⟩, hp⟩, ⟨⟨hσ', hm', hq'⟩, hp'⟩⟩
  refine .inr fun r r' h1 h2 => ?_
  have e1 : Eval c f vs r := by
    rcases h1 with ⟨he, hr⟩ | ⟨t, w, ht, he, hw, rfl⟩
    · exact .clause hfn hmem hσ hm hq hp hr he
    · exact .ensFails hfn hmem hσ hm hq hp ht he hw
  have e2 : Eval c f vs r' := by
    rcases h2 with ⟨he, hr⟩ | ⟨t, w, ht, he, hw, rfl⟩
    · exact .clause hfn hmem' hσ' hm' hq' hp' hr he
    · exact .ensFails hfn hmem' hσ' hm' hq' hp' ht he hw
  exact hd _ _ _ _ e1 e2

open EvalFunctional in
/-- A term has one result under each substitution where every function has at most one result;
so does every term inside it. -/
theorem EvalTerm.functional_hdet_of_fnDet {c : Semantics} (hd : FnDet c) {σ : Subst} {t : Term}
    {r : Option GroundTerm} (h : EvalTerm c σ t r) : (∀ r', EvalTerm c σ t r' → r = r') ∧ HDet c σ t :=
  EvalTerm.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun n σ p b _ => M6 c n σ p b)
    (fun hfn hmem hσ hmatch hreq hprio hrhs hens _ _ _ _ => fun r' h' =>
      hd _ _ _ _ (.clause hfn hmem hσ hmatch hreq hprio hrhs hens) h')
    (fun hfn hnone _ => fun r' h' => hd _ _ _ _ (.rest hfn hnone) h')
    (fun hfn hmem hσ hmatch hreq hprio ht he hw _ _ _ => fun r' h' =>
      hd _ _ _ _ (.ensFails hfn hmem hσ hmatch hreq hprio ht he hw) h')
    (fun _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (leaf rfl fun r' h' => by cases h'; rfl)
    (leaf rfl fun r' h' => by cases h'; rfl)
    (fun _ ih => case_inj ih)
    (fun hk _ ihts => case_ctor hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hk hhk hp hr ihts)
    (fun hk hhk _ hvs hf hp ihts ihf => case_call hk hhk hvs hp hf.isOvl_false ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hk hhk hvs hp ihts)
    (fun hk ho _ ihts => case_ovl hk ho ihts)
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
    h

/-- A term has one result under each substitution where every function has at most one
result. -/
theorem EvalTerm.functional_of_fnDet {c : Semantics} (hd : FnDet c) {σ : Subst} {t : Term}
    {r r' : Option GroundTerm} (h : EvalTerm c σ t r) (h' : EvalTerm c σ t r') : r = r' :=
  (EvalTerm.functional_hdet_of_fnDet hd h).1 r' h'

end KCore
