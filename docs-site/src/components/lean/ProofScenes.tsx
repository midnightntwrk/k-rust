'use client'

// Lesson "Proving a property": peano's statements and their proofs. Goal states are Lean's own
// printing, captured by elaborating KcoreSpec/PeanoProofs.lean with the info trees on (the
// generator's Goals.lean); heartbeats are measured in the same run. The proofs are those of the
// unattended loop run (lesson 7): generic theorems in StepDecide.lean, whose side conditions are one
// kernel decision on peano's data.

import { type GoalStep, goals, heartbeats, kHb, lean, lineOf, source, span } from './data'
import { goalLines, goalSource, LessonScene, type Pane, type Step } from './LessonScene'
import styles from './Lesson.module.css'

const props = source('PeanoProperties')
const proofs = source('PeanoProofs')
const evaluation = source('Evaluation')
const nomatch = '_private.0.KCore.Peano.Ground.pred_nomatch'

/** The captured tactic step of `theorem` whose text starts with `prefix` (the n-th such). */
function tac(theorem: string, prefix: string, n = 0): GoalStep {
  const hits = goals(theorem).filter((s) => s.text.trimStart().startsWith(prefix))
  if (!hits[n]) throw new Error(`lean lessons: ${theorem} has no tactic step ${n} starting ${JSON.stringify(prefix)}`)
  return hits[n]
}
const tacticName = (s: GoalStep) => {
  const text = s.text.split('\n')[0].replace(/\s+/g, ' ').trim()
  return text.length > 56 ? `${text.slice(0, 55)}…` : text
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

// ---- 2. One decision on the data ----------------------------------------------------------------

export function ChecksScene() {
  const decide = tac('_private.0.KCore.Peano.Ground.checks', 'decide +kernel')
  const goal = before(decide)
  const steps: Step[] = [
    { say: <>Every proof on this page rests on facts about peano's data: which constructor each rule's left-hand side has, what each right-hand side writes, the sorts of a few terms, two computed steps.</>, hl: { p: span(proofs, 'abbrev PeanoChecks : Prop :=', '(lookupSig peanoCore.ctorSigs "Lblz").isSome = true') }, panes: ['p'] },
    { say: <>They are written as one proposition, <code>PeanoChecks</code>: a conjunction of computations on the data that should each give <code>true</code>, or a value.</>, hl: { p: span(proofs, 'abbrev PeanoChecks : Prop :=', '(lookupSig peanoCore.ctorSigs "Lblz").isSome = true') }, panes: ['p', 'g'] },
    { say: <>One <code>decide +kernel</code> proves all of it: the kernel evaluates each computation on peano's data and finds the expected result.</>, hl: { p: [lineOf(proofs, 'private theorem checks : PeanoChecks := by decide +kernel')], g: goalLines(goal, '⊢ PeanoChecks') }, panes: ['p', 'g'] },
    { say: <>The proofs then take the facts they need from <code>checks</code> by position: <code>checks.1</code>, <code>checks.2.1</code>, and so on.</>, hl: { p: [lineOf(proofs, 'private theorem nd'), lineOf(proofs, 'private theorem sortZ'), lineOf(proofs, 'private theorem kcell')] }, panes: ['p'] },
    { say: <>This decision is most of the cost of peano's proofs: {kHb(heartbeats('checks'))} thousand heartbeats, against {kHb(heartbeats('deterministic'))} for the determinism proof that uses it.</>, hl: { p: [lineOf(proofs, 'private theorem checks : PeanoChecks := by decide +kernel')] }, panes: ['p'] },
  ]
  return (
    <LessonScene
      title="One decision on the data"
      panes={[
        { id: 'p', label: "peano's proofs", source: proofs },
        { id: 'g', label: 'The goal the kernel decides', source: goal },
      ]}
      steps={steps}
      questions={[
        { q: 'Why one decision for all the facts, not one per fact?',
          a: <>The kernel evaluates many of them through the same lookups in peano's data. In one decision that work is shared; the loop of lesson 7 found that merging them was cheaper.</> },
        { q: <>Could <code>PeanoChecks</code> be false and the proofs still build?</>,
          a: <>No. <code>decide +kernel</code> succeeds only if the kernel's evaluation gives <code>true</code>; otherwise <code>checks</code> does not check, and nothing that uses it does.</> },
      ]}
    />
  )
}

// ---- 3. Determinism --------------------------------------------------------------------------

export function DeterminismScene() {
  const det = source('detTheorem')
  const keys = source('deterministicOf')
  const steps: Step[] = [
    { say: <><code>deterministic_of</code> is proved once, for every definition: if every rule has a constructor at one position of its left-hand side, and no two rules have the same one there, then a configuration has at most one successor.</>, hl: { t: span(det, 'theorem deterministic_of', "(x y y' : Config c)") }, panes: ['t', 'k'] },
    { say: <>Its hypothesis is a computation, <code>headsApart</code>: it walks the rules once, keeping the constructors seen so far as bits of a number, and fails on a repeat.</>, hl: { k: span(keys, 'noncomputable def headsApart', 'rest (seen ||| 1 <<< key m f)') }, panes: ['t', 'k'] },
    { say: <>No two rules are compared with each other, so its cost grows with the number of rules, not with the number of pairs.</>, hl: { k: span(keys, 'noncomputable def key', 's.toByteArray.data.toList.foldl') }, panes: ['t', 'k'] },
    { say: <>For peano the position is the operand of <code>run</code>: <code>s(N)</code> in one rule, <code>z</code> in the other. <code>checks.1</code> is that fact.</>, hl: { p: [lineOf(proofs, 'headsApart [0, 0, 0, 0] 2 peanoCore.rules 0 = true'), ...span(proofs, 'theorem deterministic', 'StepDecide.deterministic_of _ _ checks.1')] }, panes: ['p'] },
    { say: <>The proof of peano's determinism is that one line. It costs {kHb(heartbeats('deterministic'))} thousand heartbeats on top of <code>checks</code>.</>, hl: { p: span(proofs, 'theorem deterministic', 'StepDecide.deterministic_of _ _ checks.1') }, panes: ['p'] },
  ]
  return (
    <LessonScene
      title="Determinism: a theorem once, a computation per definition"
      panes={[
        { id: 't', label: 'Proved once, for every definition', source: det },
        { id: 'k', label: 'The computation it asks for', source: keys },
        { id: 'p', label: "peano's proof", source: proofs },
      ]}
      steps={steps}
      questions={[
        { q: <>Add a rule <code>run(s(N)) =&gt; done(N)</code> to peano. What happens to this proof?</>,
          a: <>Two rules now have <code>s</code> under <code>run</code>, so <code>headsApart</code> finds a repeat, <code>checks</code> fails, and the proof does not build. The statement is also false: <code>run(s(z))</code> would have two successors.</> },
        { q: 'Does this theorem cover every deterministic definition?',
          a: <>No: some definitions are deterministic for reasons other than distinct constructors at one position. For those, a different theorem is needed; the statement stays the same.</> },
      ]}
    />
  )
}

// ---- 4. The equations of pred ---------------------------------------------------------------

export function EquationsScene() {
  const app1 = source('matchApp1')
  const exf = tac(nomatch, 'exfalso')
  const app = tac(nomatch, 'obtain ⟨_, rfl, h₂⟩')
  const nil = tac(nomatch, 'obtain ⟨rfl, -⟩')
  const panes: Pane[] = [
    { id: 'p', label: 'The proofs', source: proofs },
    { id: 'e', label: 'The constructors they use', source: evaluation },
    { id: 'm', label: 'A generic matching lemma', source: app1 },
    { id: 'g', label: 'Goal state', source: after(exf) },
  ]
  const steps: Step[] = [
    { say: <><code>pred_succ</code> is a term: the constructor <code>Eval.clause</code>, applied to one proof per premise.</>, hl: { p: span(proofs, 'theorem pred_succ', '.clause (pre := [])'), e: span(evaluation, '| clause {f : String}', '(hrhs : EvalTerm c σ cl.rhs v) : Eval c f vs v') }, panes: ['p', 'e'] },
    { say: <>The lookup of <code>pred</code> comes from <code>checks</code>; the clause list splits as <code>[] ++ cl :: []</code> by <code>rfl</code>; and no clause comes before it.</>, hl: { p: [lineOf(proofs, '.clause (pre := [])')], e: [lineOf(evaluation, '(hfn : c.lookupFn f = some fn)'), lineOf(evaluation, '(hcls : fn.clauses = pre ++ cl :: post)'), lineOf(evaluation, "(hpre : ∀ cl' ∈ pre, matchTerms c cl'.pats vs = none)")] }, panes: ['p', 'e'] },
    { say: <>The match is a generic lemma: a pattern <code>f(X0)</code> matches <code>f(M)</code> with X0 bound to M, for any <code>f</code> and <code>M</code>.</>, hl: { m: span(app1, 'theorem matchTerms_app1', 'matchTerms c [.app f [.var 0]]') }, panes: ['p', 'm'] },
    { say: <><code>pred_owise</code> needs one fact: the clause does not match <code>N</code> when <code>N</code> is not <code>s</code> of anything. Suppose it matched.</>, hl: { p: span(proofs, 'private theorem pred_nomatch', 'exfalso'), g: goalLines(after(exf), 'h : matchTerms', '⊢ False') }, text: { g: after(exf) }, panes: ['p', 'g'] },
    { say: <>Unfolding the match: <code>N</code> would be <code>Lbls</code> applied to some list of arguments.</>, hl: { p: [lineOf(proofs, 'obtain ⟨_, rfl, h₂⟩')], g: goalLines(after(app), 'hN : ∀ (M : GroundTerm), GroundTerm.ctor "Lbls"') }, text: { g: after(app) }, panes: ['p', 'g'] },
    { say: <>…with exactly one argument. Then <code>hN</code> says <code>s(w)</code> is not <code>s</code> of anything, which <code>hN _ rfl</code> contradicts.</>, hl: { p: span(proofs, 'obtain ⟨rfl, -⟩', 'exact hN _ rfl'), g: goalLines(after(nil), 'hN : ∀ (M : GroundTerm), GroundTerm.ctor "Lbls" [') }, text: { g: after(nil) }, panes: ['p', 'g'] },
    { say: <>With that, <code>Eval.owise</code> applies: no clause matches, the catch-all exists, and its right-hand side <code>z</code> is a constructor term. Costs: {kHb(heartbeats('pred_succ'))}, {kHb(heartbeats('pred_nomatch'))} and {kHb(heartbeats('pred_owise'))} thousand heartbeats.</>, hl: { p: span(proofs, 'theorem pred_owise', '.owise lfPred'), e: span(evaluation, '| owise {f : String}', '(hrhs : EvalTerm c (argSubst 0 vs) o.rhs v) : Eval c f vs v') }, panes: ['p', 'e'] },
  ]
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

// ---- 5. Invariants -------------------------------------------------------------------------------

export function InvariantScene() {
  const ctr = source('ctrRule')
  const ctrOf = source('counterOf')
  const value = source('valueAtSpec')
  const th = 'doneHoldsZero_preserved'
  const intro = tac(th, 'obtain ⟨r, hr, σ, hm, he⟩')
  const split = tac(th, 'rcases Bool.or_eq_true_iff')
  const head = tac(th, "obtain ⟨w, hw, hf'⟩")
  const pin = tac(th, "have h' := StepDecide.valueAt_spec")
  if (split.goalsAfter.length !== 2) throw new Error('lean lessons: the doneHoldsZero proof no longer splits into two cases')
  const steps: Step[] = [
    { say: <>"Every step keeps the counter cell" holds for any definition whose rules all copy that cell from left to right. <code>ctrRule</code> checks this of one rule, by looking at its two sides.</>, hl: { r: span(ctr, 'noncomputable def ctrRule', '| _, _ => false') }, panes: ['r', 't'] },
    { say: <><code>counter_preserved_of</code> is proved once: if every rule passes <code>ctrRule</code>, every step keeps the counter.</>, hl: { t: span(ctrOf, 'theorem counter_preserved_of', '∃ k, y.val = .ctor') }, panes: ['r', 't'] },
    { say: <>For peano, <code>checks.2.1</code> says both rules pass; the proof is one application. It costs {kHb(heartbeats('counter_preserved'))} thousand heartbeats.</>, hl: { p: [lineOf(proofs, 'peanoCore.rules.all ctrRule = true'), ...span(proofs, 'theorem counter_preserved', 'StepDecide.counter_preserved_of checks.2.1')] }, panes: ['p'] },
    { say: <><code>doneHoldsZero_preserved</code> is a short tactic proof. After opening the step, the goal is: the value <code>v</code> under <code>done</code> in <code>y</code> is <code>z</code>.</>, hl: { p: span(proofs, 'theorem doneHoldsZero_preserved', 'obtain ⟨r, hr, σ, hm, he⟩ := h'), g: goalLines(after(intro), 'he : EvalTerm', '⊢ v = natVal z') }, text: { g: after(intro) }, panes: ['p', 'g'] },
    { say: <><code>checks</code> also says, for each rule, either "it writes something other than <code>done</code> there" or "it writes the value <code>z</code> there". Splitting on it gives one goal per case.</>, hl: { p: [lineOf(proofs, 'abbrev PeanoKCell'), lineOf(proofs, 'rcases Bool.or_eq_true_iff')], g: goalLines(after(split), 'hc :') }, text: { g: after(split) }, panes: ['p', 'g'] },
    { say: <>First case: the rule writes some constructor <code>f</code> other than <code>done</code>. A generic lemma says the result has <code>f</code> there, so it cannot be <code>done(v)</code>, and the kernel finishes the contradiction.</>, hl: { p: span(proofs, "obtain ⟨w, hw, hf'⟩", 'exact absurd hc (by decide +kernel)'), v: span(value, 'theorem headAtRhs_spec', '∃ w, gsubAt path y') }, text: { g: after(head) }, panes: ['p', 'v'] },
    { say: <>Second case: the rule writes a value its left-hand side pins, here <code>z</code>. <code>valueAt_spec</code> says the result has that value there, so <code>v</code> is <code>z</code>. Cost: {kHb(heartbeats(th))} thousand heartbeats.</>, hl: { p: span(proofs, "have h' := StepDecide.valueAt_spec", "exact Option.some.inj h'"), v: span(value, 'theorem valueAt_spec', 'gsubAt path y = some g := by'), g: goalLines(after(pin), "h' :") }, text: { g: after(pin) }, panes: ['p', 'v', 'g'] },
  ]
  return (
    <LessonScene
      title="Invariants from generic lemmas"
      panes={[
        { id: 'r', label: 'A check on one rule', source: ctr },
        { id: 't', label: 'Proved once, for every definition', source: ctrOf },
        { id: 'p', label: "peano's proofs", source: proofs },
        { id: 'v', label: 'What a right-hand side puts at a position', source: value },
        { id: 'g', label: 'Goal state', source: after(intro) },
      ]}
      steps={steps}
      questions={[
        { q: <>Why does <code>counter_preserved</code> need its hypothesis <code>counterIs ctr x</code>?</>,
          a: <>Without it the statement would claim that every configuration after a step has counter <code>ctr</code>, for every <code>ctr</code>: false. The generic lemma uses it as the value being copied.</> },
        { q: 'What does either proof prove about peano specifically?',
          a: <>Nothing beyond the facts in <code>checks</code>: the rules are data, the reasoning is in lemmas proved once for every definition, and the per-definition part is a computation the kernel runs.</> },
      ]}
    />
  )
}

// ---- 6. Non-vacuity witnesses ------------------------------------------------------------------

export function WitnessScene() {
  const step = source('stepOf')
  const steps: Step[] = [
    { say: <><code>step_run_succ</code>: there are configurations <code>run(s(z))</code> and <code>run(z)</code>, with the counter of the initial configuration, and a step between them.</>, hl: { s: span(props, 'def step_run_succ.statement', '∃ x y : Config, x.val = cfg (run (s z)) ctr0') }, panes: ['s', 'p'] },
    { say: <><code>stepAt</code> computes the successor of a term by one rule: match the left-hand side, evaluate the right-hand side. <code>step_of</code> says a computed successor is a step.</>, hl: { t: [...span(step, 'noncomputable def stepAt', 'c.rules[i]?.bind'), ...span(step, 'theorem step_of', '{x y : Config c} (h : stepAt c i x.val = some y.val)')] }, panes: ['t', 'p'] },
    { say: <>For peano, <code>checks</code> contains <code>stepAt peanoCore 0 (run(s(z))) = some (run(z))</code>; the witness also needs each configuration's sort, also from <code>checks</code>.</>, hl: { p: [lineOf(proofs, 'stepAt peanoCore 0 (cfg (run (s z)) ctr0)'), ...span(proofs, 'theorem step_run_succ', 'StepDecide.step_of nd 0')] }, panes: ['p'] },
    { say: <><code>stuck_done</code>: <code>noHead</code> checks that no rule's left-hand side has the constructor <code>done(z)</code> has at the operand position, and <code>stuck_of</code> turns that into "no step".</>, hl: { t: span(step, 'noncomputable def noHead', '(y : Config c) : ¬ Step c x y'), p: span(proofs, 'theorem stuck_done', 'StepDecide.stuck_of') }, panes: ['t', 'p'] },
    { say: <><code>doneHoldsZero_fails</code>: <code>done(s(z))</code> is a configuration that does not satisfy the predicate, so the invariant is not true of everything.</>, hl: { s: span(props, 'def doneHoldsZero_fails.statement', '∃ x : Config, x.val = cfg (done (natVal (s z))) ctr0'), p: span(proofs, 'theorem doneHoldsZero_fails', 'fun h => checks') }, panes: ['s', 'p'] },
  ]
  return (
    <LessonScene
      title="Witnesses that the statements are not empty"
      panes={[
        { id: 's', label: 'The witnesses', source: props },
        { id: 't', label: 'Steps and stuckness, computed', source: step },
        { id: 'p', label: 'Their proofs', source: proofs },
      ]}
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

// ---- 7. What the proofs cost ---------------------------------------------------------------------

const perProof: { decl: string; what: string }[] = [
  { decl: 'checks', what: 'one decision: every fact about the data' },
  { decl: 'deterministic', what: 'determinism' },
  { decl: 'pred_succ', what: 'pred(s(N)) = N' },
  { decl: 'pred_nomatch', what: 'the clause of pred does not match' },
  { decl: 'pred_owise', what: 'pred(N) = z, N not s(_)' },
  { decl: 'doneHoldsZero_preserved', what: 'invariant: done holds z' },
  { decl: 'counter_preserved', what: 'invariant: counter kept' },
  { decl: 'step_run_succ', what: 'witness: run(s(z)) steps' },
  { decl: 'step_run_zero', what: 'witness: run(z) steps' },
  { decl: 'stuck_done', what: 'witness: done(z) is stuck' },
  { decl: 'doneHoldsZero_fails', what: 'witness: done(s(z)) fails' },
]

export function CostScene() {
  const all = Object.values(lean.heartbeats).reduce((sum, h) => sum + h, 0)
  const max = Math.max(...perProof.map((p) => heartbeats(p.decl)))
  const steps: Step[] = [
    { say: <>Each declaration's cost, in thousands of heartbeats: the elaborator's and the kernel's work, counted on one thread when the file was elaborated for this page.</> },
    { say: <>The decision on the data costs most. Everything else is a few applications of lemmas proved once.</> },
    { say: <>The whole file, including the definitions of <code>PeanoChecks</code> and small helper facts, costs {kHb(all)} thousand heartbeats.</> },
    { say: <>None of these numbers is in a statement. Lesson 7 shows how an unattended loop brought them here, judged only by the kernel.</> },
  ]
  return (
    <LessonScene
      title="What the proofs cost"
      panes={[]}
      steps={steps}
      delay={4200}
      visual={(at) => (
        <div className={styles.tableWrap}>
          <table className={styles.table}>
            <thead>
              <tr><th scope="col">Declaration</th><th scope="col" className={styles.num}>kHb</th><th scope="col" className={styles.barCell} aria-label="relative size" /></tr>
            </thead>
            <tbody>
              {perProof.map((p) => {
                const hb = heartbeats(p.decl)
                const on = at === 1 ? p.decl === 'checks' : undefined
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
              <tr><td>whole file</td><td className={styles.num}>{kHb(all)}</td><td /></tr>
            </tfoot>
          </table>
        </div>
      )}
      questions={[
        { q: 'Which of these costs comes back with every new property a user proves?',
          a: <>The per-proof rows, and a larger decision on the data if the new proof needs new facts. The generic lemmas are paid once for every definition.</> },
        { q: 'Can a cheaper proof make a statement weaker?',
          a: <>No. The statement is a fixed definition; the kernel checks any new proof against it. A loop changes proofs and lemmas only.</> },
      ]}
    />
  )
}
