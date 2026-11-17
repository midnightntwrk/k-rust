/-
  KCore. The step and the theory's rule and function axioms of a plain definition, kept under their
  own names: `RuleReqFails₀`, `NotApplies₀`, `Step₀` (over `EvalTerm₀`, EvalOld.lean), `StepIs₀`,
  `applies₀`, `prioRuleK₀`, and the function equations `fnItems₀` with their parts, each the
  declaration of the same name without `₀`, read for a definition whose rules have no existential
  variable and no predicate and whose left sides bind every variable. Where the definition is plain
  each is the current one (`fnItems_plain`).
-/
import KcoreSpec.EvalOld
import KcoreSpec.Faithful

set_option autoImplicit false

namespace KCore

open ML
open KoreAML (R existsAll varList)

/-! ## The step -/

/-- `RuleReqFails₀ c σ r`: the rule has a `requires` whose result under σ is not `true`. -/
inductive RuleReqFails₀ (c : Semantics) (σ : Subst) (r : Rule) : Prop where
  | intro {t : Term} {v : Option GroundTerm} (ht : r.req = some t) (he : EvalTerm₀ c σ t v)
      (hv : v ≠ some (bool true)) : RuleReqFails₀ c σ r

/-- `NotApplies₀ c r x`: rule r does not apply to x: under every well-sorted σ under which its
left-hand side denotes x, its `requires` evaluates to something other than `true`. -/
def NotApplies₀ (c : Semantics) (r : Rule) (x : GroundTerm) : Prop :=
  ∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x → RuleReqFails₀ c σ r

inductive Step₀ (c : Semantics) : Config c → Config c → Prop where
  | rule {x y : Config c} (r : Rule) (mem : r ∈ c.rules) (σ : Subst)
      (hσ : c.WellSorted r.vars σ)
      (hmatch : PatVal c σ r.lhs x.val)
      (hreq : ∀ t, r.req = some t → EvalTerm₀ c σ t (some (bool true)))
      (heval : EvalTerm₀ c σ r.rhs (some y.val))
      (hens : ∀ t, r.ens = some t → EvalTerm₀ c σ t (some (bool true)))
      (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies₀ c r' x.val) : Step₀ c x y

/-- `StepIs₀ c ref`: `ref` lists exactly the configurations `Step₀` reaches in one step. -/
def StepIs₀ (c : Semantics) (ref : StepFn) : Prop :=
  ∀ (x : Config c) (y : GroundTerm), y ∈ ref x.val ↔ ∃ hy : c.sortOf y = some topCellSort, Step₀ c x ⟨y, hy⟩


/-! ## The rules' and functions' axioms -/

/-- `∃x̄'. (lhs' ∧ ⌈req' = true⌉)`, every variable of the rule bound. -/
def applies₀ (c : Semantics) (r : Rule) (rp : RulePres) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := KoreAML.varList (r.vars.map c.sortName) rp.names
  KoreAML.existsAll C (vs.map KoreAML.Var.kore)
    (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))])


open Faithful

/-- A rule's axiom with its priority read, its right side `rhs ∧ ens`. -/
def prioRuleK₀ (c : Semantics) (r : Rule) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies₀ c r' (canonRulePres r')
  let right : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
  let rightDef : Kore.Pattern := .ceil C C right
  if comps.isEmpty then
    .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), rightDef]) right
  else .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
      .not C (anyOfC C comps), rightDef]) right

def exclusion₀ (c : Semantics) (f : Fn) (cl : Clause) (cp : ClausePres) : Kore.Pattern :=
  let ren := varList (cl.vars.map c.sortName) cp.exclNames
  existsAll R (ren.map KoreAML.Var.kore)
    (premise (f.args.map c.sortName) (cl.req.map (Term.kore c ren)) (Term.koreList c ren cl.pats))

/-- A clause with no competitor: `⌈req = true⌉ ∧ X̄ ∈ p̄ → f(X̄) = rhs ∧ ens`, the equation
`clauseAx` writes; `ens` is `⌈E = true⌉` for an `ensures` E, `⊤` without one. -/
def clauseEquation₀ (c : Semantics) (f : Fn) (cl : Clause) : Kore.Sentence :=
  let vs := canonVars c cl.vars
  eqnSentence c f (premise (f.args.map c.sortName) (cl.req.map (Term.kore c vs)) (Term.koreList c vs cl.pats))
    (Term.kore c vs cl.rhs) (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c vs)))

/-- A clause under the negation of the clauses `others`: it applies where none of them does, its
own `requires` holds and its patterns match. Its right side is `rhs ∧ ens`, as `clauseEquation₀`'s. -/
def competingEquation₀ (c : Semantics) (f : Fn) (others : List Clause) (cl : Clause) : Kore.Sentence :=
  let vs := canonVars c cl.vars
  eqnSentence c f
    (competingPremise (f.args.map c.sortName) (others.map fun cl' => exclusion₀ c f cl' (canonClausePres cl'))
      (cl.req.map (Term.kore c vs)) (Term.koreList c vs cl.pats))
    (Term.kore c vs cl.rhs) (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c vs)))

/-- The clauses of f of a smaller priority than cl's: those that apply before it. -/
def lowerClauses₀ (f : Fn) (cl : Clause) : List Clause := f.clauses.filter (·.prio < cl.prio)

/-- A clause's equation, `premise ∧ ¬ ⋁ lower → f(X̄) = rhs`: the clauses of a smaller priority
negated (`competingEquation₀`), and where there is none, the clause's premise alone
(`clauseEquation₀`). -/
def prioEquation₀ (c : Semantics) (f : Fn) (cl : Clause) : Kore.Sentence :=
  if (lowerClauses₀ f cl).isEmpty then clauseEquation₀ c f cl
  else competingEquation₀ c f (lowerClauses₀ f cl) cl

/-- A function's equations: one per clause (`prioEquation₀`). The equations of the clauses of one
priority do not exclude one another: where two apply they are coherent (`ClausesAgree`,
`MatchIndependent`, assumed by `Hyp`), which is what lets `Eval`'s unordered reading of them be
the meaning of the set of equations. An `[owise]` equation is the clause of priority 200, its
competitors the clauses of a smaller priority, which is how kompile writes it (`clauseAx`,
Emit.lean). -/
def fnEquationsK₀ (c : Semantics) (f : Fn) : List Kore.Sentence := f.clauses.map (prioEquation₀ c f)

def fnItems₀ (c : Semantics) : List KoreAML.Item :=
  c.allFns.flatMap fun f => kernelItems (fnEquationsK₀ c f)

/-- The function equations are the old ones where the definition is plain. -/
theorem flatMap_congr_mem {α β : Type} {P Q : α → List β} :
    ∀ (l : List α), (∀ a ∈ l, P a = Q a) → l.flatMap P = l.flatMap Q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      flatMap_congr_mem l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem fnItems_plain {c : Semantics} (hp : c.plain = true) : fnItems c = fnItems₀ c := by
  unfold fnItems fnItems₀
  refine flatMap_congr_mem _ fun f hf => ?_
  have hB := Semantics.binds_of_plain_mem hp hf
  have hA := Semantics.aside_of_plain_mem hp hf
  have hP := Semantics.pre_of_plain_mem hp hf
  unfold fnEquationsK fnEquationsK₀
  refine congrArg kernelItems (List.map_congr_left fun cl hcl => ?_)
  have hlow : lowerClauses f cl = lowerClauses₀ f cl :=
    List.filter_congr fun cl' h => by simp [hA cl' h]
  have hex : (lowerClauses f cl).map (fun cl' => exclusion c f cl' (canonClausePres cl')) =
      (lowerClauses₀ f cl).map (fun cl' => exclusion₀ c f cl' (canonClausePres cl')) := by
    rw [hlow]
    exact List.map_congr_left fun cl' h' =>
      exclusion_top _ (hP cl' (List.mem_filter.mp h').1) (hB cl' (List.mem_filter.mp h').1)
  show (if (lowerClauses f cl).isEmpty then clauseEquation c f cl
    else competingEquation c f (lowerClauses f cl) cl) = _
  rw [clauseEquation_top (hP cl hcl), competingEquation_top (hP cl hcl)]
  unfold prioEquation₀
  rw [hex, hlow]
  rfl


/-! ## The step and the rule axioms are the old ones where the rules are plain -/

/-- A plain definition's rule has the plain shapes. -/
theorem Semantics.plain_rule {c : Semantics} (hp : c.plain = true) {r : Rule} (hr : r ∈ c.rules) :
    r.exs = [] ∧ r.pre = .top ∧ r.post = .top ∧ binds r.vars.length (varOccs r.lhs) = true := by
  simp only [Semantics.plain, Bool.and_eq_true, List.all_eq_true] at hp
  obtain ⟨⟨⟨hex, hpre⟩, hpost⟩, hb⟩ := hp.1.1.1.1 r hr
  exact ⟨List.isEmpty_iff.mp hex, Cond.eq_top_of_isTop hpre, Cond.eq_top_of_isTop hpost, hb⟩

theorem notApplies_of_binds {c : Semantics} {r : Rule} (hp : c.plain = true) (x : GroundTerm)
    (h : (r.pre.isTop && binds r.vars.length (varOccs r.lhs)) = true) : NotApplies c r x ↔ NotApplies₀ c r x := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨hpt, hb⟩ := h
  constructor
  · intro hn σ hσ hm
    obtain ⟨t, v, ht, he, hv⟩ := (hn σ (hσ.at _) hm).req_of_top (Cond.eq_top_of_isTop hpt)
    exact .intro ht (EvalTerm.to_old (Semantics.aside_of_plain hp) he) hv
  · intro hn σ hσ hm
    cases hn σ (Rule.wellSorted_of_at hb hσ) hm with
    | intro ht he hv => exact .intro ht (EvalTerm₀.to_new (Semantics.binds_of_plain hp) he) hv

theorem applies_of_binds (c : Semantics) (r : Rule) (rp : RulePres)
    (h : (r.pre.isTop && binds r.vars.length (varOccs r.lhs)) = true) : applies c r rp = applies₀ c r rp := by
  simp only [Bool.and_eq_true] at h
  rw [applies_top rp (Cond.eq_top_of_isTop h.1) h.2]
  rfl

/-- The rule axioms are the old ones where the definition is plain. -/
theorem prioRuleK_plain {c : Semantics} (hp : c.plain = true) (r : Rule) (hr : r ∈ c.rules) :
    prioRuleK c r = prioRuleK₀ c r := by
  obtain ⟨hex, hpre, hpost, -⟩ := Semantics.plain_rule hp hr
  have hcomps : (c.rules.filter (·.prio < r.prio)).map (fun r' => applies c r' (canonRulePres r')) =
      (c.rules.filter (·.prio < r.prio)).map (fun r' => applies₀ c r' (canonRulePres r')) := by
    apply List.map_congr_left
    intro r' hr'
    obtain ⟨-, hpre', -, hb'⟩ := Semantics.plain_rule hp (List.mem_filter.mp hr').1
    exact applies_of_binds c r' _ (by simp [hpre', hb', Cond.isTop])
  simp only [prioRuleK, prioRuleK₀, ruleRight, hcomps, hex, hpre, hpost, Cond.conj, Cond.isTop, if_true,
    List.filterMap_nil, List.foldr_nil, List.append_nil, List.cons_append, List.nil_append]

/-- **The step is the old step** where the rules are plain. -/
theorem step_plain {c : Semantics} (hp : c.plain = true) (x y : Config c) : Step c x y ↔ Step₀ c x y := by
  have hna : ∀ r' ∈ c.rules, NotApplies c r' x.val ↔ NotApplies₀ c r' x.val := fun r' hr' => by
    obtain ⟨-, hpre', -, hb'⟩ := Semantics.plain_rule hp hr'
    exact notApplies_of_binds hp x.val (by simp [hpre', hb', Cond.isTop])
  constructor
  · intro h
    cases h with
    | rule r mem σ hσ hm hreq _ he hens _ hprio =>
      exact .rule r mem σ hσ hm (fun t ht => EvalTerm.to_old (Semantics.aside_of_plain hp) (hreq t ht))
        (EvalTerm.to_old (Semantics.aside_of_plain hp) he)
        (fun t ht => EvalTerm.to_old (Semantics.aside_of_plain hp) (hens t ht))
        (fun r' hr' hlt => (hna r' hr').mp (hprio r' hr' hlt))
  · intro h
    cases h with
    | rule r mem σ hσ hm hreq he hens hprio =>
      obtain ⟨-, hpre, hpost, -⟩ := Semantics.plain_rule hp mem
      exact Step.rule_top r mem σ hpre hpost hσ hm
        (fun t ht => EvalTerm₀.to_new (Semantics.binds_of_plain hp) (hreq t ht))
        (EvalTerm₀.to_new (Semantics.binds_of_plain hp) he)
        (fun t ht => EvalTerm₀.to_new (Semantics.binds_of_plain hp) (hens t ht)) (fun r' hr' hlt => (hna r' hr').mpr (hprio r' hr' hlt))


/-! ## The statements over the plain step -/

/-- Soundness over the plain step: the theory `Γ` with the step's closure has a model, and every
step of `Step₀` is a theorem of `Γ`, `⟦x⟧ → •⟦y⟧`. -/
def SoundC₀ (c : Semantics) : Prop :=
  (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c)) ∧
  ∀ x y : Config c, Step₀ c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val))
/-- Completeness over the plain step, for a step function `ref` that lists `Step₀`'s successors:
with the step's closure every successor of x is one `ref` lists. -/
def CompleteC₀ (c : Semantics) (ref : StepFn) : Prop :=
  StepIs₀ c ref → ∀ x : Config c,
    (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (den c))))

end KCore
