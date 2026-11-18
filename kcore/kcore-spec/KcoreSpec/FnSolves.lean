/-
  KCore. Sufficient conditions for `FnSolves` (EvalFunctional.lean): with `FnDet`, it follows from
  two conditions on the clauses of a function that has more than one priority or more than one
  clause deciding at a point.

  - `PrioDecided`: where a clause applies, each `requires` of a matching clause of a smaller
    priority has a result and that clause's predicate a truth value. Then "no clause of a smaller priority applies" is "each of them fails"
    (`Fails`), which is what `Eval.clause` asks, so every result of the deciding clause's right-hand
    side is a result of the function.
  - `CoDefined`: of two clause instances that decide at one point, if one has a value, the other
    has a result (`Clause.InstRes`: its right-hand side's where its `ensures` is `true`, none
    where the `ensures` has another result). A value of the function comes from a clause instance that
    decides (a smaller priority applying contradicts the deciding clause, a larger one has the
    deciding clause failing); `CoDefined` gives the deciding clause's right-hand side a result,
    and `FnDet` makes it that value.

  With `PrioDecided` and a result (`Clause.Res`) of each clause at each match under which it decides,
  `FnDet` gives `FnSolves` for clauses with existential variables too (`fnSolves_of_res`): the
  function's result there is the clause's (`Clause.Res.eval`), and it is the one result.

  `PrioDecided` is vacuous for a function with one priority, `CoDefined` where two deciding
  instances are one instance; a semantics whose functions all have results at arguments of their
  sorts (`FnTerminates`) meets both (`prioDecided_of_total`, `coDefined_of_total`, ModelPat.lean).
-/
import KcoreSpec.EvalFunctional

set_option autoImplicit false

namespace KCore

/-- Where a clause applies, each `requires` of a matching clause of a smaller priority that is not
`aside` has a result, and that clause's predicate a truth value. -/
def PrioDecided (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, ∀ vs cl σ, cl ∈ fn.clauses → cl.AppliesAt c σ vs →
    ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats vs →
      (∀ t, cl'.req = some t → ∃ r, EvalTerm c σ' t r) ∧ ∃ b, Holds c cl'.vars.length σ' cl'.pre b

/-- A clause instance's result under σ: its right-hand side's where its `ensures` evaluates to
`true` (or it has none), none where its `ensures` has another result. -/
def Clause.InstRes (c : Semantics) (cl : Clause) (σ : Subst) (r : Option GroundTerm) : Prop :=
  ((∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) ∧ EvalTerm c σ cl.rhs r) ∨
    ∃ t w, cl.ens = some t ∧ EvalTerm c σ t w ∧ w ≠ some (bool true) ∧ r = none

/-- Two clause instances that decide at one point: if one has a value, the other has a result. -/
def CoDefined (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, ∀ vs cl σ cl' σ', cl ∈ fn.clauses → cl' ∈ fn.clauses →
    cl.DecidesAt c fn σ vs → cl'.DecidesAt c fn σ' vs →
    (∃ v, cl.InstRes c σ (some v)) → ∃ r, cl'.InstRes c σ' r

variable {c : Semantics}

/-- A clause without existential variables that applies under σ does not fail, its `requires`
having one result there. -/
theorem not_fails_of_applies (hd : FnDet c) {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    (hex : cl.exs = []) (ha : cl.AppliesAt c σ vs) (hf : Fails c vs cl) : False := by
  cases hf with
  | intro h =>
    cases h σ (((wellSortedAt_univ hex).mp ha.1).at _) ha.2.1 with
    | intro ht he hr => exact hr (EvalTerm.functional_of_fnDet hd he (ha.2.2.1 _ ht))
    | pre hf => exact absurd (Holds.functional_of_fnDet hd ha.2.2.2 hf) (by simp)

/-- A clause that fails at `vs` has no instance there, over the substitutions `Fails` ranges over,
whose `requires` evaluates to `true`, where every function has at most one result. -/
theorem not_true_of_fails (hd : FnDet c) {vs : List GroundTerm} {cl : Clause} (hf : Fails c vs cl)
    {σ : Subst} (hw : c.WellSortedAt cl.vars cl.leftVars σ) (hp : PatVals c σ cl.pats vs)
    (hq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpr : Holds c cl.vars.length σ cl.pre true) : False := by
  cases hf with
  | intro h =>
    cases h σ hw hp with
    | intro ht he hr => exact hr (EvalTerm.functional_of_fnDet hd he (hq _ ht))
    | pre hf => exact absurd (Holds.functional_of_fnDet hd hpr hf) (by simp)

/-- A clause none of whose instances applies at `vs` fails there, where each matching instance's
`requires` has a result; the instances range over the substitutions well sorted on the variables
of its patterns and conditions, as `Fails` does. -/
theorem fails_of_not_applies {vs : List GroundTerm} {cl : Clause}
    (hres : ∀ σ, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs →
      (∀ t, cl.req = some t → ∃ r, EvalTerm c σ t r) ∧ ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hno : ∀ σ, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs →
      ¬ ((∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) ∧
         Holds c cl.vars.length σ cl.pre true)) : Fails c vs cl := by
  refine .intro fun σ hσ hp => ?_
  obtain ⟨hres', b, hb⟩ := hres σ hσ hp
  cases b with
  | false => exact .pre hb
  | true =>
    cases hq : cl.req with
    | none => exact (hno σ hσ hp ⟨fun t ht => (by rw [hq] at ht; cases ht), hb⟩).elim
    | some t =>
      obtain ⟨r, hr⟩ := hres' t hq
      refine .intro hq hr fun he => hno σ hσ hp ⟨fun t' ht' => ?_, hb⟩
      rw [hq] at ht'; cases ht'; rw [← he]; exact hr

/-- **One function's equations are solved**, where it is the one `lookupFn` finds under its
label, every function has at most one result, its clauses have no existential variable and the
right side's predicate `\top`, and they meet `PrioDecided` and `CoDefined`'s conditions at `vs`:
where a clause decides, the function's values are that clause's right-hand side's where its
`ensures` evaluates to `true`. -/
theorem solves_of_parts {fn : Fn} (hlk : c.lookupFn fn.label = some fn) (hd : FnDet c)
    (hx : ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top) {vs : List GroundTerm}
    (hp : ∀ cl σ, cl ∈ fn.clauses → cl.AppliesAt c σ vs →
      ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats vs →
        (∀ t, cl'.req = some t → ∃ r, EvalTerm c σ' t r) ∧ ∃ b, Holds c cl'.vars.length σ' cl'.pre b)
    (ha : ∀ cl σ cl' σ', cl ∈ fn.clauses → cl' ∈ fn.clauses →
      cl.DecidesAt c fn σ vs → cl'.DecidesAt c fn σ' vs →
      (∃ v, cl.InstRes c σ (some v)) → ∃ r, cl'.InstRes c σ' r)
    {cl : Clause} (hcl : cl ∈ fn.clauses) {σ : Subst} (hdec : cl.DecidesAt c fn σ vs) (v : GroundTerm) :
    Eval c fn.label vs (some v) ↔
      EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) := by
  have hlow : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl' :=
    fun cl' hcl' ha hlt =>
      fails_of_not_applies (fun σ' hσ' hp' => hp cl σ hcl hdec.1 cl' hcl' ha hlt σ' hσ' hp')
        (hdec.2 cl' hcl' ha hlt)
  have back : ∀ r, cl.InstRes c σ r → Eval c fn.label vs r := fun r hr => by
    rcases hr with ⟨he, hr⟩ | ⟨t, w, ht, he, hw, rfl⟩
    · exact .clause hlk hcl ((wellSortedAt_univ (hx cl hcl).1).mp hdec.1.1) hdec.1.2.1 hdec.1.2.2.1 hdec.1.2.2.2 hlow (hx cl hcl).1 hr he
        (Clause.holds_postTop (hx cl hcl).2 σ)
    · exact .ensFails hlk hcl ((wellSortedAt_univ (hx cl hcl).1).mp hdec.1.1) hdec.1.2.1 hdec.1.2.2.1 hdec.1.2.2.2 hlow (hx cl hcl).1 ht he hw
  have fwd : ∀ r, Eval c fn.label vs r → ∀ v, r = some v →
      EvalTerm c σ cl.rhs (some v) ∧ ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) := by
    intro r hE
    cases hE with
    | @clause _ fn' _ cl₂ σ₂ _ hfn' hmem₂ hσ₂ hm₂ hq₂ hpr₂ hprio₂ hex₂ hr₂ he₂ hpost₂ =>
      intro v hv; subst hv
      rw [hlk] at hfn'; cases hfn'
      rcases EvalFunctional.compete_or_blocks cl₂ cl with hcomp | ⟨ha, hlt⟩ | ⟨ha, hlt⟩
      · -- the two compete: cl₂ decides as the model reads deciding, its smaller clauses failing
        have hdec₂ : cl₂.DecidesAt c fn σ₂ vs :=
          ⟨⟨hσ₂.at _, hm₂, hq₂, hpr₂⟩, fun cl' h1 h2 h3 σ' hw hp' hq' => not_true_of_fails hd (hprio₂ cl' h1 h2 h3) hw hp' hq'.1 hq'.2⟩
        obtain ⟨r, hr⟩ := ha cl₂ σ₂ cl σ hmem₂ hcl hdec₂ hdec ⟨v, .inl ⟨he₂, hr₂⟩⟩
        have := hd _ _ _ _ (back r hr) (.clause hlk hmem₂ hσ₂ hm₂ hq₂ hpr₂ hprio₂ hex₂ hr₂ he₂ hpost₂)
        subst this
        rcases hr with ⟨he, hr⟩ | ⟨_, _, _, _, _, h⟩
        · exact ⟨hr, he⟩
        · cases h
      · exact (hdec.2 cl₂ hmem₂ ha hlt σ₂ (hσ₂.at _) hm₂ ⟨hq₂, hpr₂⟩).elim
      · exact (not_fails_of_applies hd (hx cl hcl).1 hdec.1 (hprio₂ cl hcl ha hlt)).elim
    | rest hfn' hnone =>
      rw [hlk] at hfn'; cases hfn'
      exact (not_fails_of_applies hd (hx cl hcl).1 hdec.1 (hnone cl hcl)).elim
    | ensFails => intro v hv; cases hv
    | clauseEx hfn' hmem₂ _ _ _ _ _ hne₂ _ _ _ _ =>
      rw [hlk] at hfn'; cases hfn'
      exact absurd (hx _ hmem₂).1 hne₂
    | exNone => intro v hv; cases hv
  exact ⟨fun hE => fwd _ hE v rfl, fun hr => back _ (.inl ⟨hr.2, hr.1⟩)⟩

/-- **`FnDet`, `PrioDecided` and `CoDefined` give `FnSolves`**, where each function is the one
`lookupFn` finds under its label and no clause has an existential variable or a right side's
predicate other than `\top`. -/
theorem fnSolves_of_parts_lookup (hl : ∀ fn ∈ c.fns, c.lookupFn fn.label = some fn) (hd : FnDet c)
    (hx : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top)
    (hp : PrioDecided c) (ha : CoDefined c) : FnSolves c :=
  (fnSolves_iff_noExs hx).mpr fun fn hfn vs _ _ hcl _ hdec v =>
    solves_of_parts (hl fn hfn) hd (hx fn hfn) (hp fn hfn vs) (ha fn hfn vs) hcl hdec v

/-- An instance that gives the value `v` is decided as the result `r` only where `r` is `v`, where
every function has at most one result. -/
theorem instIs_of_gives (hd : FnDet c) {cl : Clause} {σ : Subst} {r : Option GroundTerm} {v : GroundTerm}
    (hi : InstIs c σ cl r) (hg : cl.Gives c σ v) : r = some v := by
  obtain ⟨hr, he, hp⟩ := hg
  cases hi with
  | fails _ h =>
    cases h with
    | ens ht he' hw => exact absurd (EvalTerm.functional_of_fnDet hd he' (he _ ht)) hw
    | post h => exact absurd (Holds.functional_of_fnDet hd hp h) (by simp)
    | rhs h => exact absurd (EvalTerm.functional_of_fnDet hd h hr) (by simp)
  | gives hr' _ _ => exact EvalTerm.functional_of_fnDet hd hr' hr

/-- **One function's equations are solved**, where it is the one `lookupFn` finds under its label,
every function has at most one result, its clauses meet `PrioDecided`'s condition at `vs`, and each
of its clauses has a result (`Clause.Res`) at each match under which it decides at `vs`: where a
clause decides under σ, the function's values are the values the instances of that clause's right
side give, at the well-sorted σ' that are σ off the existential variables the left side does not
hold. The clauses may have existential variables. -/
theorem solves_of_res {fn : Fn} (hlk : c.lookupFn fn.label = some fn) (hd : FnDet c)
    {vs : List GroundTerm}
    (hp : ∀ cl σ, cl ∈ fn.clauses → cl.AppliesAt c σ vs →
      ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats vs →
        (∀ t, cl'.req = some t → ∃ r, EvalTerm c σ' t r) ∧ ∃ b, Holds c cl'.vars.length σ' cl'.pre b)
    (hres : ∀ cl ∈ fn.clauses, ∀ σ, cl.Decides c fn σ vs → ∃ r, cl.Res c σ r)
    {cl : Clause} (hcl : cl ∈ fn.clauses) {σ : Subst} (hdec : cl.DecidesAt c fn σ vs) (v : GroundTerm) :
    Eval c fn.label vs (some v) ↔
      ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v := by
  have hD : cl.Decides c fn σ vs := ⟨hdec.1, fun cl' hcl' ha hlt =>
    fails_of_not_applies (fun σ' hσ' hp' => hp cl σ hcl hdec.1 cl' hcl' ha hlt σ' hσ' hp')
      (hdec.2 cl' hcl' ha hlt)⟩
  obtain ⟨r, hr⟩ := hres cl hcl σ hD
  have hE := hr.eval hlk hcl hD
  constructor
  · intro hv
    have hrv : r = some v := hd _ _ _ _ hE hv
    subst hrv
    rcases hr with ⟨hex, ⟨he, hpost, hr⟩ | ⟨_, _, _, _, _, h⟩⟩ | ⟨-, ⟨σ', v', ha, hw, hg, -, h⟩ | ⟨h, -⟩⟩
    · exact ⟨σ, AgreeOff.refl _ _, (wellSortedAt_univ hex).mp hdec.1.1, hr, he, hpost⟩
    · cases h
    · cases h; exact ⟨σ', ha, hw, hg⟩
    · cases h
  · rintro ⟨σ', ha, hw, hg⟩
    have hrv : r = some v := by
      rcases hr with ⟨hex, ⟨he, hpost, hr⟩ | ⟨t, w, ht, he, hw', rfl⟩⟩ |
        ⟨-, ⟨σ₀, v₀, -, -, -, hall, rfl⟩ | ⟨rfl, -, hall⟩⟩
      · exact EvalTerm.functional_of_fnDet hd hr
          (Exec.EvalTerm.congr hg.1 fun i _ => ha i (by rw [Clause.exsFree_nil hex]; exact List.not_mem_nil))
      · exact absurd (EvalTerm.functional_of_fnDet hd he
          (Exec.EvalTerm.congr (hg.2.1 t ht) fun i _ => ha i (by rw [Clause.exsFree_nil hex]; exact List.not_mem_nil))) hw'
      · exact instIs_of_gives hd (hall σ' ha hw) hg
      · exact instIs_of_gives hd (hall σ' ha hw) hg
    subst hrv; exact hE

/-- **`FnDet`, `PrioDecided` and a result of each clause where it decides give `FnSolves`**, where
each function is the one `lookupFn` finds under its label. The clauses may have existential
variables. -/
theorem fnSolves_of_res (hl : ∀ fn ∈ c.fns, c.lookupFn fn.label = some fn) (hd : FnDet c)
    (hp : PrioDecided c)
    (hres : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, ∀ vs, c.sortsOf vs = some fn.args → ∀ σ,
      cl.Decides c fn σ vs → ∃ r, cl.Res c σ r) : FnSolves c :=
  fun fn hfn vs hvs _ hcl _ hdec v =>
    solves_of_res (hl fn hfn) hd (hp fn hfn vs) (fun cl hcl σ hD => hres fn hfn cl hcl vs hvs σ hD) hcl hdec v

/-- A result of the instance of a clause without existential variables whose right side's predicate
is `\top` is a result of the clause there. -/
theorem Clause.res_of_instRes {cl : Clause} (hex : cl.exs = []) (hpost : cl.post = .top) {σ : Subst}
    {r : Option GroundTerm} (h : cl.InstRes c σ r) : cl.Res c σ r :=
  (Clause.res_noExs hex).mpr <| h.elim (fun h => .inl ⟨h.1, by rw [hpost]; exact .top, h.2⟩) .inr

/-- Every function of the definition has a result at every argument list of its sorts (`FnHyp`'s
first conjunct). -/
def FnTerminates (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ r, Eval c fn.label vs r

end KCore
