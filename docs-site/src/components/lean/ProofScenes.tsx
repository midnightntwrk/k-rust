'use client'

// Lesson "Proving a property": peano's statements and their proofs. Goal states are Lean's own
// printing, captured by elaborating KcoreSpec/PeanoProofs.lean with the info trees on (the
// generator's Goals.lean); heartbeats are measured in the same run.

import {
  type GoalStep,
  fmt,
  goalStep,
  heartbeats,
  kHb,
  lean,
  lineOf,
  source,
  span,
} from './data'
import { goalLines, goalSource, LessonScene, type Pane, type Step } from './LessonScene'
import styles from './Lesson.module.css'

const props = source('PeanoProperties')
const proofs = source('PeanoProofs')
const tactic = source('PeanoTactic')
const evaluation = source('Evaluation')

// A tactic step's label: its source text, or, inside a macro's expansion, Lean's reprint of it.
const tacticName = (s: GoalStep) => {
  const text = s.text.replace(/\s+/g, ' ').trim()
  const short = text.length > 56 ? `${text.slice(0, 55)}…` : text
  return s.canonical ? short : `${short} (inside step_cases)`
}
const after = (s: GoalStep) => goalSource(`after ${tacticName(s)}`, s.goalsAfter)
const before = (s: GoalStep) => goalSource(`before ${tacticName(s)}`, s.goalsBefore)

// ---- 1. Statements are definitions -----------------------------------------------------------

export function StatementsScene() {
  const def = (name: string) => [lineOf(props, `def ${name}`), lineOf(props, `def ${name}`) + 1].filter((l) => l <= props.end)
  const steps: Step[] = [
    { say: <>Each property is a definition of type <code>Prop</code>; its proof is a separate theorem in <code>PeanoProofs.lean</code>.</>, hl: { p: span(props, 'def deterministic.statement', 'def doneHoldsZero_fails.statement') } },
    { say: <>Determinism: a configuration has at most one successor.</>, hl: { p: def('deterministic.statement') } },
    { say: <>The two equations of <code>pred</code>, over the evaluation relation, for every ground term <code>N</code>.</>, hl: { p: [...def('pred_succ.statement'), ...def('pred_owise.statement')] } },
    { say: <>A predicate on configurations, and the invariant that every step keeps it: if the k cell holds <code>done(v)</code>, then v is <code>z</code>.</>, hl: { p: [...def('doneHoldsZero (x : Config)'), ...span(props, 'def doneHoldsZero_preserved.statement', '∀ x y : Config, Step x y → doneHoldsZero x')] } },
    { say: <>A second invariant, one that uses its hypothesis: every step keeps the counter cell.</>, hl: { p: [...def('counterIs'), ...span(props, 'def counter_preserved.statement', '∀ (ctr : GroundTerm) (x y : Config)')] } },
    { say: <>Four witnesses that the invariants are not true for an empty reason. They say that particular configurations exist and how they step.</>, hl: { p: span(props, 'def ctr0', 'doneHoldsZero_fails.statement : Prop') } },
  ]
  return (
    <LessonScene
      title="The statements"
      panes={[{ id: 'p', label: 'What is proved about peano', source: props }]}
      steps={steps}
      questions={[
        { q: <>Why is <code>pred_succ</code> stated for every ground term <code>N</code>, not only for values of sort <code>Nat</code>?</>,
          a: <>It is stronger. The typed form follows by applying it to <code>N.val</code> for any value <code>N</code> of sort <code>Nat</code>.</> },
        { q: <>What does a statement of the form <code>∀ x y, Step x y → P x → P y</code> say if <code>Step</code> relates nothing?</>,
          a: <>Nothing: it holds for every <code>P</code>. It also holds trivially if <code>P</code> is true of every configuration. The witnesses exclude both.</> },
      ]}
    />
  )
}

// ---- 2. Determinism --------------------------------------------------------------------------

export function DeterminismScene() {
  const apart = source('rulesApart')
  const theorem = source('stepDeterministic')
  const decide = goalStep('deterministic', 'decide +kernel')
  const goal = before(decide)
  const panes: Pane[] = [
    { id: 't', label: 'Proved once, for every definition', source: theorem },
    { id: 'a', label: 'The hypothesis, a computation on the data', source: apart },
    { id: 'p', label: "peano's proof", source: proofs },
    { id: 'g', label: 'The goal Lean leaves for peano', source: goal },
  ]
  const steps: Step[] = [
    { say: <><code>Step.deterministic</code> is proved once, for every definition, under one hypothesis: <code>rulesApart</code>.</>, hl: { t: span(theorem, 'theorem Step.deterministic', '(h₁ : Step c x y)') }, panes: ['t', 'a'] },
    { say: <><code>rulesApart</code> is a <code>Bool</code> computed from the rules: no two left-hand sides overlap, and no sort has two incomparable supersorts.</>, hl: { a: span(apart, 'def rulesApart : Bool :=', 'c.noDiamonds && (pairs') }, panes: ['t', 'a'] },
    { say: <>peano's proof is that theorem, applied to <code>peanoCore</code>.</>, hl: { p: span(proofs, 'theorem deterministic', 'fun _ _ _ => Step.deterministic') }, panes: ['p', 'g'] },
    { say: <>What is left is this goal, exactly as Lean prints it.</>, hl: { g: goalLines(goal, '⊢ peanoCore.rulesApart = true') }, panes: ['p', 'g'] },
    { say: <><code>decide +kernel</code> evaluates <code>rulesApart</code> on peano's data in the kernel and gets <code>true</code>; Lean computes the same (<code>{String(lean.facts.rulesApart)}</code>).</>, hl: { p: [lineOf(proofs, 'fun _ _ _ => Step.deterministic')] }, panes: ['p', 'g'] },
    { say: <>Cost: {kHb(heartbeats('deterministic'))} thousand heartbeats, nearly all of it that decision, over every pair of rules and every pair of subsort pairs.</>, hl: { p: [lineOf(proofs, 'fun _ _ _ => Step.deterministic')] }, panes: ['p', 'g'] },
  ]
  return (
    <LessonScene
      title="Determinism: a theorem once, a decision per definition"
      panes={panes}
      steps={steps}
      questions={[
        { q: <>Add a third rule <code>run(s(N)) =&gt; done(N)</code> to peano. What happens to this proof?</>,
          a: <>Its left-hand side overlaps <code>runSucc</code>'s, so <code>rulesApart</code> computes <code>false</code>, the kernel's decision fails, and the proof does not check. The statement would also be false: <code>run(s(z))</code> would have two successors.</> },
        { q: <>Why does <code>rulesApart</code> also ask for no diamonds in the subsort order?</>,
          a: <>The overlap check treats injections from incomparable sorts as apart. That is sound only when no sort lies below two incomparable sorts, so the condition asks for it.</> },
      ]}
    />
  )
}

// ---- 3. The equations of pred ---------------------------------------------------------------

export function EquationsScene() {
  const have = goalStep('pred_owise', 'have hm')
  const exfalso = goalStep('pred_owise', 'exfalso')
  const simp = goalStep('pred_owise', 'simp only [ts')
  const subst = goalStep('pred_owise', 'subst_vars')
  const owise = goalStep('pred_owise', 'exact .owise')
  const start = goalStep('pred_owise', 'by')
  const goal0 = before(start)
  const panes: Pane[] = [
    { id: 'p', label: 'The proofs', source: proofs },
    { id: 'e', label: 'The constructors they use', source: evaluation },
    { id: 'g', label: 'Goal state', source: goal0 },
  ]
  const steps: Step[] = [
    { say: <><code>pred_succ</code> is a term: the constructor <code>Eval.clause</code>, applied to one proof per premise.</>, hl: { p: span(proofs, 'theorem pred_succ', '.clause (fn := predFn)'), e: span(evaluation, '| clause {f : String}', '(hrhs : EvalTerm c σ cl.rhs v) : Eval c f vs v') }, panes: ['p', 'e'] },
    { say: <>The lookup finds <code>predFn</code> and its clause list splits as <code>[] ++ cl :: []</code>: both by <code>rfl</code>, Lean evaluating the data.</>, hl: { p: [lineOf(proofs, '.clause (fn := predFn)')], e: [lineOf(evaluation, '(hfn : c.lookupFn f = some fn)'), lineOf(evaluation, '(hcls : fn.clauses = pre ++ cl :: post)')] }, panes: ['p', 'e'] },
    { say: <>No clause comes before it, so the premise "no earlier clause matches" is about an empty list: <code>fun _ h =&gt; nomatch h</code>.</>, hl: { p: [lineOf(proofs, '.clause (fn := predFn)')], e: [lineOf(evaluation, "(hpre : ∀ cl' ∈ pre, matchTerms c cl'.pats vs = none)")] }, panes: ['p', 'e'] },
    { say: <>The match and the value of X0 are <code>rfl</code> too: for any <code>N</code>, matching <code>s(X0)</code> against <code>s(N)</code> unfolds to <code>[(0, N)]</code>.</>, hl: { p: [lineOf(proofs, '.clause (fn := predFn)')], e: [lineOf(evaluation, '(hmatch : matchTerms c cl.pats vs = some σ)'), lineOf(evaluation, '(hrhs : EvalTerm c σ cl.rhs v) : Eval c f vs v')] }, panes: ['p', 'e'] },
    { say: <><code>pred_owise</code> has a hypothesis: <code>N</code> is not <code>s</code> of anything. The goal is <code>Pred N z</code>.</>, hl: { p: [lineOf(proofs, 'theorem pred_owise')], g: goalLines(goal0, 'hN :', '⊢ Pred N z') }, panes: ['p', 'g'] },
    { say: <>First it proves that the clause does not match <code>N</code>; the case where the match gives some σ must be impossible.</>, hl: { p: span(proofs, 'have hm : matchTerms', 'exfalso'), g: goalLines(after(exfalso), 'h : matchTerms', '⊢ False') }, text: { g: after(exfalso) }, panes: ['p', 'g'] },
    { say: <>Unfolding the match turns that hypothesis into equations: <code>N</code> would be <code>Lbls</code> applied to something.</>, hl: { p: [lineOf(proofs, 'simp only [ts, matchTerms_cons')], g: goalLines(after(simp), 'v = GroundTerm.ctor "Lbls" vs') }, text: { g: after(simp) }, panes: ['p', 'g'] },
    { say: <>After splitting and substituting, <code>hN</code> says that <code>s(w)</code> is not <code>s</code> of anything, which <code>hN _ rfl</code> contradicts.</>, hl: { p: span(proofs, 'destruct_hyps', 'exact hN _ rfl'), g: goalLines(after(subst), 'hN : ∀ (M : GroundTerm), GroundTerm.ctor "Lbls" [w✝] ≠ s M') }, text: { g: after(subst) }, panes: ['p', 'g'] },
    { say: <>With <code>hm</code> in hand, <code>Eval.owise</code> applies: no clause matches, the catch-all exists, and its right-hand side <code>z</code> is a constructor term.</>, hl: { p: span(proofs, 'exact .owise (fn := predFn)', '(.ctor rfl .nil)'), e: span(evaluation, '| owise {f : String}', '(hrhs : EvalTerm c (argSubst 0 vs) o.rhs v) : Eval c f vs v'), g: goalLines(before(owise), 'hm : matchTerms') }, text: { g: before(owise) }, panes: ['p', 'e', 'g'] },
    { say: <>Costs: {kHb(heartbeats('pred_succ'))} and {kHb(heartbeats('pred_owise'))} thousand heartbeats.</>, hl: { p: [lineOf(proofs, 'theorem pred_succ'), lineOf(proofs, 'theorem pred_owise')] }, panes: ['p', 'g'] },
  ]
  if (have.goalsAfter.length !== 1) throw new Error('lean lessons: pred_owise’s have should leave one goal')
  return (
    <LessonScene
      title="The equations of pred"
      panes={panes}
      steps={steps}
      questions={[
        { q: <><code>pred_succ</code> has no hypothesis on <code>N</code>. Why does it hold when <code>N</code> is not of sort <code>Nat</code>?</>,
          a: <>Matching does not check the sorts of variables, so <code>s(X0)</code> matches <code>s(N)</code> for every ground term <code>N</code>.</> },
        { q: <>Is the value of <code>pred(s(N))</code> unique, or could <code>Eval</code> give it two values?</>,
          a: <>Unique, by the generic theorem <code>Eval.det</code>, proved once with no hypothesis: the first matching clause is determined by the arguments.</> },
      ]}
    />
  )
}

// ---- 4. Invariants by the per-rule tactic ------------------------------------------------------

export function InvariantScene() {
  const intro = goalStep('counter_preserved', 'intro ctr x y h')
  const obtain = goalStep('counter_preserved', 'obtain  ⟨  r  ,  hr')
  const unfold = goalStep('counter_preserved', 'simp  only  [  KCore.Peano.Ground.rules_eq')
  const split = goalStep('counter_preserved', "repeat'")
  const invert = goalStep('counter_preserved', 'all_goals  (')
  const closeEach = goalStep('counter_preserved', 'all_goals exact')
  const doneInvert = goalStep('doneHoldsZero_preserved', 'all_goals  (')
  const doneRfl = goalStep('doneHoldsZero_preserved', 'all_goals rfl')
  if (split.goalsAfter.length !== 2 || invert.goalsAfter.length !== 2 || doneInvert.goalsAfter.length !== 0 || doneRfl.goalsBefore.length !== 0) {
    throw new Error('lean lessons: the per-rule tactic no longer leaves the goals this scene describes')
  }
  const g = (s: GoalStep) => after(s)
  const panes: Pane[] = [
    { id: 'p', label: 'The proofs', source: proofs },
    { id: 't', label: 'The tactic, given peano’s rules by name', source: tactic },
    { id: 'g', label: 'Goal state', source: g(intro) },
  ]
  const steps: Step[] = [
    { say: <>After <code>intro</code>: a step <code>h : Step x y</code>, the counter <code>ctr</code> of <code>x</code>, and the goal that <code>y</code> has it too.</>, hl: { p: span(proofs, 'theorem counter_preserved', 'intro ctr x y h'), g: goalLines(g(intro), 'h : Step x y', '⊢ counterIs ctr y') }, panes: ['p', 'g'] },
    { say: <><code>peano_step_cases</code> is the generic <code>step_cases</code> with peano's rules, named and checked against the data by <code>rfl</code>.</>, hl: { t: [lineOf(tactic, 'theorem rules_eq'), ...span(tactic, 'macro "peano_step_cases "', 'KCore.Peano.tz, KCore.Peano.tpred')] }, panes: ['p', 't'] },
    { say: <>Inside it, first: <code>h</code> is opened into its rule, the rule's membership, σ, the match and the evaluation.</>, hl: { g: goalLines(g(obtain), 'hr✝ : r✝ ∈ peanoCore.rules', 'hm✝ :', 'he✝ :') }, text: { g: g(obtain) }, panes: ['g'] },
    { say: <>Unfolding <code>rules_eq</code> turns the membership into a disjunction: the rule is <code>runSucc</code> or <code>runZero</code>, as data.</>, hl: { g: goalLines(g(unfold), 'hr✝ :', '∨') }, text: { g: g(unfold) }, panes: ['g'] },
    { say: <>Splitting it gives one goal per rule: <code>case inl</code> for <code>runSucc</code>, <code>case inr</code> for <code>runZero</code>.</>, hl: { g: goalLines(g(split), 'case inl', 'case inr') }, text: { g: g(split) }, panes: ['g'] },
    { say: <>Inverting the match and the evaluation rewrites <code>x</code> and <code>y</code> into the rule's two sides. The call of <code>pred</code> stays a hypothesis, <code>Eval … "Lblpred" …</code>.</>, hl: { g: goalLines(g(invert), 'Eval peanoCore "Lblpred"', '⊢ counterIs w✝²', '⊢ counterIs w✝') }, text: { g: g(invert) }, panes: ['g'] },
    { say: <>In both cases the counter of <code>y</code> is the variable copied from <code>x</code>, so <code>exact ⟨_, rfl⟩</code> closes each.</>, hl: { p: [lineOf(proofs, 'all_goals exact ⟨_, rfl⟩')] }, text: { g: goalSource('goals after: all_goals exact ⟨_, rfl⟩', closeEach.goalsAfter) }, panes: ['p', 'g'] },
    { say: <>For <code>doneHoldsZero_preserved</code> the same tactic closes both cases itself: <code>runSucc</code> writes <code>run(…)</code>, which clashes with <code>done(v)</code>, and <code>runZero</code> writes <code>done(inj{'{'}Nat,Val{'}'}(z))</code>.</>, hl: { p: span(proofs, 'theorem doneHoldsZero_preserved', 'all_goals rfl') }, text: { g: goalSource('goals after the tactic, in doneHoldsZero_preserved', doneInvert.goalsAfter) }, panes: ['p', 'g'] },
    { say: <>So the proof's <code>all_goals rfl</code> runs on no goal at all. Costs: {kHb(heartbeats('counter_preserved'))} and {kHb(heartbeats('doneHoldsZero_preserved'))} thousand heartbeats.</>, hl: { p: [lineOf(proofs, 'all_goals rfl'), lineOf(proofs, 'all_goals exact ⟨_, rfl⟩')] }, panes: ['p', 'g'] },
  ]
  return (
    <LessonScene
      title="Invariants, one goal per rule"
      panes={panes}
      steps={steps}
      questions={[
        { q: <>Why does <code>counter_preserved</code> need its hypothesis <code>counterIs ctr x</code>?</>,
          a: <>Without it the statement would claim that every configuration after a step has counter <code>ctr</code>, for every <code>ctr</code>: false. The proof uses it as the copied variable.</> },
        { q: <>In <code>case inl</code> the value of <code>pred(s(w))</code> stays unknown. Why is that enough here?</>,
          a: <>The counter is in another cell, copied from <code>x</code> by the rule's variable X2. Only an invariant about the k cell would need the value, and then the tactic can be given the equation <code>pred_succ</code> to rewrite it.</> },
        { q: 'What does the tactic prove about peano specifically?',
          a: <>Nothing: the rules are data, and the split and the inversions use generic lemmas. The per-definition part is the names of the rules and the subsort list, each checked against the data.</> },
      ]}
    />
  )
}

// ---- 5. Non-vacuity witnesses ------------------------------------------------------------------

export function WitnessScene() {
  const sortGoal = goalStep('step_run_succ', 'decide +kernel', 0)
  const hs = goalStep('step_run_succ', 'have hs')
  const refine = goalStep('step_run_succ', 'refine')
  const rw = goalStep('step_run_succ', 'rw [hs]')
  const stuck = goalStep('stuck_done', 'have hs')
  const panes: Pane[] = [
    { id: 's', label: 'The witnesses', source: props },
    { id: 'p', label: 'Their proofs', source: proofs },
    { id: 'g', label: 'Goal state', source: before(sortGoal) },
  ]
  const steps: Step[] = [
    { say: <><code>step_run_succ</code>: there are configurations <code>run(s(z))</code> and <code>run(z)</code>, with the counter of the initial configuration, and a step between them.</>, hl: { s: span(props, 'def step_run_succ.statement', '∃ x y : Config, x.val = cfg (run (s z)) ctr0') }, panes: ['s', 'p'] },
    { say: <>Building <code>x</code> needs a proof that its term has the configuration sort; the kernel decides it.</>, hl: { p: [lineOf(proofs, 'let x : Config := ⟨cfg (run (s z)) ctr0')], g: goalLines(before(sortGoal), '⊢ peanoCore.sortOf') }, panes: ['p', 'g'] },
    { say: <>Then the kernel runs the executable step on <code>x</code>: <code>successors peanoCore x = [y]</code>.</>, hl: { p: [lineOf(proofs, 'have hs : successors peanoCore x = [y]')], g: goalLines(after(hs), 'hs : successors peanoCore x = [y]') }, text: { g: after(hs) }, panes: ['p', 'g'] },
    { say: <><code>step_iff</code>, with <code>evalReady</code> decided, turns <code>Step x y</code> into <code>y ∈ successors peanoCore x</code>.</>, hl: { p: [lineOf(proofs, 'refine ⟨x, y, rfl, rfl, (step_iff')], g: goalLines(after(refine), '⊢ y ∈ successors peanoCore x') }, text: { g: after(refine) }, panes: ['p', 'g'] },
    { say: <>Rewriting with <code>hs</code> leaves <code>y ∈ [y]</code>.</>, hl: { p: [lineOf(proofs, 'rw [hs]')], g: goalLines(after(rw), '⊢ y ∈ [y]') }, text: { g: after(rw) }, panes: ['p', 'g'] },
    { say: <><code>stuck_done</code> goes the same way with <code>successors = []</code>: no <code>y</code> can be in the empty list.</>, hl: { s: span(props, 'def stuck_done.statement', '∃ x : Config, x.val = cfg (done (natVal z)) ctr0 ∧ ∀ y'), p: [lineOf(proofs, 'have hs : successors peanoCore x = []')] }, text: { g: after(stuck) }, panes: ['s', 'p', 'g'] },
    { say: <><code>doneHoldsZero_fails</code>: <code>done(s(z))</code> is a configuration that does not satisfy the predicate, so the invariant is not true of everything.</>, hl: { s: span(props, 'def doneHoldsZero_fails.statement', '∃ x : Config, x.val = cfg (done (natVal (s z))) ctr0'), p: span(proofs, 'theorem doneHoldsZero_fails', 'fun h => absurd') }, panes: ['s', 'p'] },
  ]
  return (
    <LessonScene
      title="Witnesses that the statements are not empty"
      panes={panes}
      steps={steps}
      questions={[
        { q: 'Why does each witness prove that its terms have the configuration sort?',
          a: <>Because it states that a <code>Config</code> exists. Without that proof the witness could not be built, and a term of the wrong sort cannot make the statement true by accident.</> },
        { q: <>Which witness rules out a <code>Step</code> that relates every configuration to something?</>,
          a: <><code>stuck_done</code>: the configuration <code>done(z)</code> has no successor.</> },
      ]}
    />
  )
}

// ---- 6. What the proofs cost ---------------------------------------------------------------------

const perProof: { decl: string; what: string; table?: string }[] = [
  { decl: 'deterministic', what: 'determinism', table: 'tableDeterminism' },
  { decl: 'pred_succ', what: 'pred(s(N)) = N', table: 'tablePredSucc' },
  { decl: 'pred_owise', what: 'pred(N) = z, N not s(_)', table: 'tablePredOwise' },
  { decl: 'doneHoldsZero_preserved', what: 'invariant: done holds z', table: 'tableDoneHoldsZero' },
  { decl: 'counter_preserved', what: 'invariant: counter kept', table: 'tableCounter' },
  { decl: 'step_run_succ', what: 'witness: run(s(z)) steps' },
  { decl: 'step_run_zero', what: 'witness: run(z) steps' },
  { decl: 'stuck_done', what: 'witness: done(z) is stuck' },
  { decl: 'doneHoldsZero_fails', what: 'witness: done(s(z)) fails' },
]

const once: { key: string; what: string }[] = [
  { key: 'detGeneric', what: 'determinism theorem, match lemmas, Eval.det' },
  { key: 'tacticGeneric', what: 'the per-rule tactic step_cases' },
  { key: 'tacticSupport', what: 'its evaluation-inversion lemmas' },
  { key: 'executionTheory', what: 'soundness, fuel sufficiency, step_iff' },
  { key: 'executionWf', what: 'wf implies evalReady' },
  { key: 'namesApart', what: 'wf keeps names apart' },
]

export function CostScene() {
  const max = Math.max(...perProof.map((p) => heartbeats(p.decl)))
  const total = perProof.reduce((sum, p) => sum + heartbeats(p.decl), 0)
  const witnesses = ['step_run_succ', 'step_run_zero', 'stuck_done', 'doneHoldsZero_fails']
  const focus: (readonly string[] | null)[] = [null, ['doneHoldsZero_preserved'], ['counter_preserved'], ['deterministic'], witnesses, null]
  const steps: Step[] = [
    { say: <>Each proof's cost, in thousands of heartbeats: the elaborator's and the kernel's work, counted on one thread when the file was elaborated for this page.</> },
    { say: <>The <code>doneHoldsZero</code> invariant costs most: substitutions through every hypothesis, and one kernel decision per right-hand-side head (constructor or function).</> },
    { say: <>The counter invariant costs about half as much; it has no hypothesis about the k cell to compare with.</> },
    { say: <>Determinism is one kernel decision of <code>rulesApart</code>, which grows with the square of the number of rules.</> },
    { say: <>The witnesses pay for kernel evaluation of the executable step, where every symbol comparison is a string comparison.</> },
    { say: <>None of these numbers is in a statement. A loop may lower any of them by changing proofs and tactics; that is the planned lesson 7.</> },
  ]
  return (
    <LessonScene
      title="What the proofs cost"
      panes={[]}
      steps={steps}
      delay={4200}
      visual={(at) => (
        <>
          <div className={styles.tableWrap}>
            <table className={styles.table}>
              <thead>
                <tr><th scope="col">Proof (per definition)</th><th scope="col" className={styles.num}>kHb</th><th scope="col" className={styles.barCell} aria-label="relative size" /></tr>
              </thead>
              <tbody>
                {perProof.map((p) => {
                  const hb = heartbeats(p.decl)
                  const on = focus[at] ? focus[at]!.includes(p.decl) : undefined
                  return (
                    <tr key={p.decl} className={on ? styles.on : on === false ? styles.off : ''}>
                      <td><code>{p.decl}</code><br /><span className={styles.small}>{p.what}</span></td>
                      <td className={styles.num}>{kHb(hb)}</td>
                      <td className={styles.barCell}><div className={styles.bar} style={{ width: `${(hb / max) * 100}%` }} title={`${p.decl}: ${kHb(hb)} kHb`} /></td>
                    </tr>
                  )
                })}
              </tbody>
              <tfoot>
                <tr><td>total</td><td className={styles.num}>{kHb(total)}</td><td /></tr>
                <tr><td colSpan={3} className={styles.small}>Paid once per definition besides: the tactic's per-definition part (rule names, subsort list), {fmt(lean.oneTime.tacticPeano)} kHb in the cost table.</td></tr>
              </tfoot>
            </table>
          </div>
          <div className={styles.tableWrap}>
            <table className={styles.table}>
              <thead>
                <tr><th scope="col">Proved once, for every definition</th><th scope="col" className={styles.num}>kHb</th></tr>
              </thead>
              <tbody>
                {once.map((o) => (
                  <tr key={o.key}><td>{o.what}</td><td className={styles.num}>{fmt(lean.oneTime[o.key])}</td></tr>
                ))}
              </tbody>
            </table>
          </div>
        </>
      )}
      questions={[
        { q: 'Which of these costs comes back with every new property a user proves?',
          a: <>The per-proof rows. The second table is paid once, for every definition, and the frozen definitions and data cost {fmt(lean.oneTime.frozenPerDefinition)} thousand heartbeats per definition, which no loop may change.</> },
        { q: 'Can a cheaper proof make a statement weaker?',
          a: <>No. The statement is a fixed definition; the kernel checks any new proof against it. A loop changes proofs and tactics only.</> },
      ]}
    />
  )
}

/** The cost rows measured when this page's data was generated, beside the earlier cost table's. */
export function CostAgreement() {
  const rows = perProof.filter((p) => p.table)
  return (
    <div className={styles.tableWrap}>
      <table className={styles.table}>
        <thead>
          <tr><th scope="col">Proof</th><th scope="col" className={styles.num}>measured for this page</th><th scope="col" className={styles.num}>earlier cost table</th></tr>
        </thead>
        <tbody>
          {rows.map((p) => (
            <tr key={p.decl}><td><code>{p.decl}</code></td><td className={styles.num}>{kHb(heartbeats(p.decl))}</td><td className={styles.num}>{fmt(lean.oneTime[p.table!])}</td></tr>
          ))}
        </tbody>
      </table>
    </div>
  )
}
