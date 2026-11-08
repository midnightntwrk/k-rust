'use client'

// Lesson 5: peano's statements and their proofs. Goal states are Lean's own printing, captured by
// elaborating KcoreSpec/PeanoProofs.lean with the info trees on (the generator's Goals.lean);
// heartbeats are measured in the same run. The proofs are those of the unattended loop run
// (lesson 7): generic theorems in StepDecide.lean, whose side conditions are one kernel decision on
// peano's data.

import { type GoalStep, goals, heartbeats, kHb, lean, lineOf, source, span, type Source } from '../data'
import { type Lesson, note } from '../lesson'
import { numbers } from '../numbers'
import { A, Arrow, Bar, Box, Label, Rows, Small, Svg } from '../viz'

/** A goal state as a pane source: Lean's own printing, numbered from 1. */
const goalSource = (label: string, states: readonly string[]): Source => {
  const text = states.length ? states.join('\n\n') : 'no goals'
  return { file: label, start: 1, end: text.split('\n').length, text }
}

/** The lines (1-based) of a goal-state source that contain any of the needles; each needle must occur. */
const goalLines = (src: Source, ...needles: string[]): number[] => {
  const rows = src.text.split('\n')
  const out = new Set<number>()
  for (const needle of needles) {
    let found = false
    rows.forEach((row, i) => {
      if (row.includes(needle)) {
        out.add(i + 1)
        found = true
      }
    })
    if (!found) throw new Error(`lean lessons: goal state ${src.file} has no line containing ${JSON.stringify(needle)}`)
  }
  return [...out].sort((a, b) => a - b)
}

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

const def = (name: string) => [lineOf(props, `def ${name}`), lineOf(props, `def ${name}`) + 1].filter((l) => l <= props.end)

const decide = tac('_private.0.KCore.Peano.Ground.checks', 'decide +kernel')
const decideGoal = before(decide)

const det = source('detTheorem')
const keys = source('deterministicOf')

const app1 = source('matchApp1')
const exf = tac(nomatch, 'exfalso')
const appStep = tac(nomatch, 'obtain ⟨_, rfl, h₂⟩')
const nil = tac(nomatch, 'obtain ⟨rfl, -⟩')

const ctr = source('ctrRule')
const ctrOf = source('counterOf')
const valueAt = source('valueAtSpec')
const th = 'doneHoldsZero_preserved'
const intro = tac(th, 'obtain ⟨r, hr, σ, hm, he⟩')
const split = tac(th, 'rcases Bool.or_eq_true_iff')
const head = tac(th, "obtain ⟨w, hw, hf'⟩")
const pin = tac(th, "have h' := StepDecide.valueAt_spec")
if (split.goalsAfter.length !== 2) throw new Error('lean lessons: the doneHoldsZero proof no longer splits into two cases')

const stepOf = source('stepOf')

const shape = (at: number) => (
  <Svg viewBox="0 0 900 400" label="Every proof has three parts: a theorem proved once, one kernel decision on the data, and an application of the theorem">
    <Box x={160} y={170} w={250} h={90} text="a theorem, proved once" sub="for every definition" tone={at === 1 ? 'on' : 'plain'} sans size={15} />
    <A show={at >= 2}>
      <Box x={460} y={170} w={250} h={90} text="one kernel decision" sub="on the definition's data" tone={at === 2 ? 'on' : 'plain'} sans size={15} />
      <Arrow x1={285} y1={170} x2={335} y2={170} on={at === 2} />
    </A>
    <A show={at >= 3}>
      <Box x={750} y={170} w={210} h={90} text="an application" sub="of one to the other" tone={at === 3 ? 'accent' : 'plain'} sans size={15} />
      <Arrow x1={585} y1={170} x2={645} y2={170} on={at === 3} />
    </A>
    <A show={at === 0}>
      <Label x={450} y={60} anchor="middle" size={16} weight={600} text="“Every step keeps the counter cell.”" />
      <Label x={450} y={90} anchor="middle" size={13} tone="var(--muted)" text="about every configuration, including ones no test will reach" />
    </A>
  </Svg>
)

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
const allHb = Object.values(lean.heartbeats).reduce((sum, h) => sum + h, 0)
const maxHb = Math.max(...perProof.map((p) => heartbeats(p.decl)))

const costs = (at: number) => (
  <Rows
    head={['Declaration', { text: 'kHb', num: true }, { text: '', bar: true }]}
    rows={perProof.map((p) => {
      const hb = heartbeats(p.decl)
      return {
        key: p.decl,
        state: at === 1 ? (p.decl === 'checks' ? 'cur' : 'faded') : undefined,
        cells: [<span key="d">{p.decl}<br /><Small>{p.what}</Small></span>, kHb(hb), <Bar key="b" pct={(hb / maxHb) * 100} title={`${p.decl}: ${kHb(hb)} kHb`} />],
      }
    })}
    foot={['whole file', kHb(allHb), '']}
  />
)

export const lesson5: Lesson = {
  id: 'proving-a-property',
  number: 5,
  title: 'Proving a property',
  scenes: [
    {
      id: 'p1',
      title: 'One shape for every proof',
      visual: shape,
      frames: [
        { say: "A run of `peano.k` shows one path. This lesson states properties that speak about every configuration, over the `Step` of lesson 4, and proves them. You'll see the goals exactly as Lean prints them while the proofs run." },
        { say: "Every proof here has the same shape. First, a theorem proved ==once, for every definition==, that reduces the property to a computation on the definition's data." },
        { say: "Second, one kernel decision that runs those computations on peano's data." },
        { say: "Third, an application of the theorem to the decided facts. These aren't the first proofs written for these statements: an unattended loop rewrote them, judged only by the kernel, and made them much cheaper. Lesson 7 tells that story." },
      ],
    },
    {
      id: 'p2',
      title: 'The statements',
      panes: [{ id: 'p', label: 'What is proved about peano', source: props }],
      frames: [
        { hl: { p: span(props, 'def deterministic.statement', 'def doneHoldsZero_fails.statement') }, say: "Each property is a definition of type `Prop`; its proof is a separate theorem in `PeanoProofs.lean`. A statement is fixed before any proof is written. Lesson 6 shows that these " + numbers.module('PeanoProperties') + " lines, with the definitions they use, are what a reader has to read." },
        { hl: { p: def('deterministic.statement') }, notes: [note('p', lineOf(props, 'def deterministic.statement'), "Determinism: a configuration has at most one successor.")] },
        {
          hl: { p: [...def('pred_succ.statement'), ...def('pred_owise.statement')] },
          notes: [note('p', lineOf(props, 'def pred_succ.statement'), "The two equations of `pred`, over the evaluation relation, for every ground term `N`.")],
          ask: {
            q: "Why is `pred_succ` stated for every ground term `N`, not only for values of sort `Nat`?",
            options: ["Sort `Nat` is not available in Lean", "It is stronger: the typed form follows by applying it to `N.val` for any value `N` of sort `Nat`", "It has to be, or it would be false"],
            answer: 1,
            why: "A statement that holds on more terms says more. The typed form is one application away.",
          },
        },
        { hl: { p: [...def('doneHoldsZero (x : Config)'), ...span(props, 'def doneHoldsZero_preserved.statement', '∀ x y : Config, Step x y → doneHoldsZero x')] }, notes: [note('p', lineOf(props, 'def doneHoldsZero (x : Config)'), "A predicate: if the k cell holds `done(v)`, then v is `z`."), note('p', lineOf(props, 'def doneHoldsZero_preserved.statement'), "The invariant: every step keeps it.")] },
        { hl: { p: [...def('counterIs'), ...span(props, 'def counter_preserved.statement', '∀ (ctr : GroundTerm) (x y : Config)')] }, notes: [note('p', lineOf(props, 'def counter_preserved.statement'), "A second invariant, one that uses its hypothesis: every step keeps the counter cell.")] },
        { hl: { p: span(props, 'def ctr0', 'doneHoldsZero_fails.statement : Prop') }, say: "Four ==witnesses== that the invariants are not true for an empty reason. They say that particular configurations exist and how they step. You'll see why they matter below." },
      ],
    },
    {
      id: 'p3',
      title: 'One decision on the data',
      panes: [
        { id: 'p', label: "peano's proofs", source: proofs },
        { id: 'g', label: 'The goal the kernel decides', source: decideGoal, lang: 'goal' },
      ],
      frames: [
        { hl: { p: span(proofs, 'abbrev PeanoChecks : Prop :=', '(lookupSig peanoCore.ctorSigs "Lblz").isSome = true') }, notes: [note('p', lineOf(proofs, 'abbrev PeanoChecks : Prop :='), "Which constructor each rule's left-hand side has, what each right-hand side writes, the sorts of a few terms, two computed steps.")], say: "Every proof rests on facts about peano's data." },
        { hl: { p: span(proofs, 'abbrev PeanoChecks : Prop :=', '(lookupSig peanoCore.ctorSigs "Lblz").isSome = true') }, notes: [note('p', lineOf(proofs, 'abbrev PeanoChecks : Prop :='), "One proposition: a conjunction of computations on the data that should each give `true`, or a value.")] },
        {
          hl: { p: [lineOf(proofs, 'private theorem checks : PeanoChecks := by decide +kernel')], g: goalLines(decideGoal, '⊢ PeanoChecks') },
          notes: [note('p', lineOf(proofs, 'private theorem checks : PeanoChecks := by decide +kernel'), "The kernel evaluates each computation on peano's data and finds the expected result.", 'decide +kernel')], say: "One decision proves all of it.",
          ask: {
            q: "Could `PeanoChecks` be false and the proofs still build?",
            options: ["Yes, if the proofs avoid the false part", "No: `decide +kernel` succeeds only if the kernel's evaluation gives `true`", "Yes, `decide` trusts the compiler"],
            answer: 1,
            why: "Otherwise `checks` does not check, and nothing that uses it does.",
          },
        },
        { hl: { p: [lineOf(proofs, 'private theorem nd'), lineOf(proofs, 'private theorem sortZ'), lineOf(proofs, 'private theorem kcell')] }, notes: [note('p', lineOf(proofs, 'private theorem nd'), "The proofs take the facts they need from `checks` by position: `checks.1`, `checks.2.1`, and so on.")] },
        { hl: { p: [lineOf(proofs, 'private theorem checks : PeanoChecks := by decide +kernel')] }, say: "This decision is most of the cost of peano's proofs: " + kHb(heartbeats('checks')) + " thousand heartbeats, against " + kHb(heartbeats('deterministic')) + " for the determinism proof that uses it." },
      ],
    },
    {
      id: 'p4',
      title: 'Determinism: a theorem once',
      panes: [
        { id: 't', label: 'Proved once, for every definition', source: det },
        { id: 'k', label: 'The computation it asks for', source: keys },
      ],
      frames: [
        { hl: { t: span(det, 'theorem deterministic_of', "(x y y' : Config c)") }, notes: [note('t', lineOf(det, 'theorem deterministic_of'), "If every rule has a constructor at one position of its left-hand side, and no two rules have the same one there, then a configuration has at most one successor.")], say: "`deterministic_of` is proved once, for every definition." },
        { hl: { k: span(keys, 'noncomputable def headsApart', 'rest (seen ||| 1 <<< key m f)') }, notes: [note('k', lineOf(keys, 'noncomputable def headsApart'), "Walks the rules once, keeping the constructors seen so far as bits of a number, and fails on a repeat.")], say: "Its hypothesis is a computation, `headsApart`." },
        { hl: { k: span(keys, 'noncomputable def key', 's.toByteArray.data.toList.foldl') }, say: "No two rules are compared with each other, so its cost grows with the number of rules, not with the number of pairs." },
      ],
    },
    {
      id: 'p5',
      title: "Determinism: peano's proof",
      panes: [{ id: 'p', label: "peano's proof", source: proofs }],
      frames: [
        { hl: { p: [lineOf(proofs, 'headsApart [0, 0, 0, 0] 2 peanoCore.rules 0 = true'), ...span(proofs, 'theorem deterministic', 'StepDecide.deterministic_of _ _ checks.1')] }, notes: [note('p', lineOf(proofs, 'headsApart [0, 0, 0, 0] 2 peanoCore.rules 0 = true'), "The position is the operand of `run`: `s(N)` in one rule, `z` in the other."), note('p', lineOf(proofs, 'StepDecide.deterministic_of _ _ checks.1'), "That fact.", 'checks.1')] },
        {
          hl: { p: span(proofs, 'theorem deterministic', 'StepDecide.deterministic_of _ _ checks.1') },
          say: "The proof of peano's determinism is ==that one line==. It costs " + kHb(heartbeats('deterministic')) + " thousand heartbeats on top of `checks`.",
          ask: {
            q: "Add a rule `run(s(N)) => done(N)` to peano. What happens to this proof?",
            options: ["It still builds, with a warning", "`headsApart` finds a repeat, `checks` fails, and the proof does not build", "Lean picks the first rule"],
            answer: 1,
            why: "And the statement is also false: `run(s(z))` would have two successors.",
          },
        },
      ],
    },
    {
      id: 'p6',
      title: 'pred_succ is a term',
      panes: [
        { id: 'p', label: 'The proofs', source: proofs },
        { id: 'e', label: 'The constructors they use', source: evaluation },
        { id: 'm', label: 'A generic matching lemma', source: app1 },
      ],
      frames: [
        { hl: { p: span(proofs, 'theorem pred_succ', '.clause (pre := [])'), e: span(evaluation, '| clause {f : String}', '(hrhs : EvalTerm c σ cl.rhs v) : Eval c f vs v') }, notes: [note('p', lineOf(proofs, 'theorem pred_succ'), "A term: the constructor `Eval.clause`, applied to one proof per premise.")] },
        { hl: { p: [lineOf(proofs, '.clause (pre := [])')], e: [lineOf(evaluation, '(hfn : c.lookupFn f = some fn)'), lineOf(evaluation, '(hcls : fn.clauses = pre ++ cl :: post)'), lineOf(evaluation, "(hpre : ∀ cl' ∈ pre, matchTerms c cl'.pats vs = none)")] }, notes: [note('e', lineOf(evaluation, '(hfn : c.lookupFn f = some fn)'), "From `checks`.", 'hfn'), note('e', lineOf(evaluation, '(hcls : fn.clauses = pre ++ cl :: post)'), "The clause list splits as `[] ++ cl :: []`, by `rfl`.", 'hcls'), note('e', lineOf(evaluation, "(hpre : ∀ cl' ∈ pre, matchTerms c cl'.pats vs = none)"), "No clause comes before it.", 'hpre')] },
        {
          hl: { m: span(app1, 'theorem matchTerms_app1', 'matchTerms c [.app f [.var 0]]') },
          notes: [note('m', lineOf(app1, 'theorem matchTerms_app1'), "A pattern `f(X0)` matches `f(M)` with X0 bound to M, for any `f` and `M`.")],
          ask: {
            q: "`pred_succ` has no hypothesis on `N`. Why does it hold when `N` is not of sort `Nat`?",
            options: ["It doesn't; the theorem is unsound there", "Matching does not check the sorts of variables, so `s(X0)` matches `s(N)` for every ground term `N`", "Lean coerces `N` to `Nat`"],
            answer: 1,
            why: "You saw this in lesson 4: sorts are checked once, on the configuration, not during matching.",
          },
        },
      ],
    },
    {
      id: 'p7',
      title: 'pred_owise, goal by goal',
      panes: [
        { id: 'p', label: 'The proofs', source: proofs },
        { id: 'g', label: 'Goal state', source: after(exf), lang: 'goal' },
      ],
      frames: [
        { hl: { p: span(proofs, 'private theorem pred_nomatch', 'exfalso'), g: goalLines(after(exf), 'h : matchTerms', '⊢ False') }, text: { g: after(exf) }, notes: [note('p', lineOf(proofs, 'private theorem pred_nomatch'), "The clause does not match `N` when `N` is not `s` of anything.")], say: "`pred_owise` needs one fact. Suppose the clause matched: the goal becomes `False`." },
        { hl: { p: [lineOf(proofs, 'obtain ⟨_, rfl, h₂⟩')], g: goalLines(after(appStep), 'hN : ∀ (M : GroundTerm), GroundTerm.ctor "Lbls"') }, text: { g: after(appStep) }, notes: [note('g', goalLines(after(appStep), 'hN : ∀ (M : GroundTerm), GroundTerm.ctor "Lbls"')[0], "Unfolding the match: `N` would be `Lbls` applied to some list of arguments.")] },
        { hl: { p: span(proofs, 'obtain ⟨rfl, -⟩', 'exact hN _ rfl'), g: goalLines(after(nil), 'hN : ∀ (M : GroundTerm), GroundTerm.ctor "Lbls" [') }, text: { g: after(nil) }, notes: [note('g', goalLines(after(nil), 'hN : ∀ (M : GroundTerm), GroundTerm.ctor "Lbls" [')[0], "Now `hN` says `s(w)` is not `s` of anything."), note('p', lineOf(proofs, 'exact hN _ rfl'), "Which this contradicts.", 'hN _ rfl')], say: "…with exactly one argument." },
      ],
    },
    {
      id: 'p8',
      title: 'The catch-all applies',
      panes: [
        { id: 'p', label: 'The proofs', source: proofs },
        { id: 'e', label: 'The constructors they use', source: evaluation },
      ],
      frames: [
        { hl: { p: span(proofs, 'theorem pred_owise', '.owise lfPred'), e: span(evaluation, '| owise {f : String}', '(hrhs : EvalTerm c (argSubst 0 vs) o.rhs v) : Eval c f vs v') }, say: "With that, `Eval.owise` applies: no clause matches, the catch-all exists, and its right-hand side `z` is a constructor term. Costs: " + kHb(heartbeats('pred_succ')) + ", " + kHb(heartbeats('pred_nomatch')) + " and " + kHb(heartbeats('pred_owise')) + " thousand heartbeats." },
      ],
    },
    {
      id: 'p9',
      title: 'An invariant from one lemma',
      panes: [
        { id: 'r', label: 'A check on one rule', source: ctr },
        { id: 't', label: 'Proved once, for every definition', source: ctrOf },
        { id: 'p', label: "peano's proofs", source: proofs },
      ],
      frames: [
        { hl: { r: span(ctr, 'noncomputable def ctrRule', '| _, _ => false') }, notes: [note('r', lineOf(ctr, 'noncomputable def ctrRule'), "Checks one rule, by looking at its two sides.")], say: "\"Every step keeps the counter cell\" holds for any definition whose rules all copy that cell from left to right." },
        { hl: { t: span(ctrOf, 'theorem counter_preserved_of', '∃ k, y.val = .ctor') }, notes: [note('t', lineOf(ctrOf, 'theorem counter_preserved_of'), "Proved once: if every rule passes `ctrRule`, every step keeps the counter.")] },
        {
          hl: { p: [lineOf(proofs, 'peanoCore.rules.all ctrRule = true'), ...span(proofs, 'theorem counter_preserved', 'StepDecide.counter_preserved_of checks.2.1')] },
          say: "For peano, `checks.2.1` says both rules pass, and the proof is one application. It costs " + kHb(heartbeats('counter_preserved')) + " thousand heartbeats.",
          ask: {
            q: "Why does `counter_preserved` need its hypothesis `counterIs ctr x`?",
            options: ["For performance", "Without it the statement would claim every configuration after a step has counter `ctr`, for every `ctr`: false", "Lean requires a hypothesis on every theorem"],
            answer: 1,
            why: "The generic lemma uses it as the value being copied.",
          },
        },
      ],
    },
    {
      id: 'p10',
      title: 'An invariant in tactics',
      panes: [
        { id: 'p', label: "peano's proofs", source: proofs },
        { id: 'g', label: 'Goal state', source: after(intro), lang: 'goal' },
      ],
      frames: [
        { hl: { p: span(proofs, 'theorem doneHoldsZero_preserved', 'obtain ⟨r, hr, σ, hm, he⟩ := h'), g: goalLines(after(intro), 'he : EvalTerm', '⊢ v = natVal z') }, text: { g: after(intro) }, notes: [note('g', goalLines(after(intro), '⊢ v = natVal z')[0], "The goal: the value `v` under `done` in `y` is `z`.", '⊢ v = natVal z')], say: "`doneHoldsZero_preserved` is a short tactic proof. Open the step." },
        { hl: { p: [lineOf(proofs, 'abbrev PeanoKCell'), lineOf(proofs, 'rcases Bool.or_eq_true_iff')], g: goalLines(after(split), 'hc :') }, text: { g: after(split) }, notes: [note('p', lineOf(proofs, 'abbrev PeanoKCell'), "For each rule, either it writes something other than `done` there, or it writes the value `z` there.")], say: "Splitting on it gives one goal per case." },
      ],
    },
    {
      id: 'p11',
      title: 'The two cases',
      panes: [
        { id: 'p', label: "peano's proofs", source: proofs },
        { id: 'v', label: 'What a right-hand side puts at a position', source: valueAt },
        { id: 'g', label: 'Goal state', source: after(head), lang: 'goal' },
      ],
      frames: [
        { hl: { p: span(proofs, "obtain ⟨w, hw, hf'⟩", 'exact absurd hc (by decide +kernel)'), v: span(valueAt, 'theorem headAtRhs_spec', '∃ w, gsubAt path y') }, text: { g: after(head) }, notes: [note('p', lineOf(proofs, "obtain ⟨w, hw, hf'⟩"), "The rule writes some constructor `f` other than `done`. A generic lemma says the result has `f` there, so it cannot be `done(v)`.")], say: "First case. The kernel finishes the contradiction." },
        { hl: { p: span(proofs, "have h' := StepDecide.valueAt_spec", "exact Option.some.inj h'"), v: span(valueAt, 'theorem valueAt_spec', 'gsubAt path y = some g := by'), g: goalLines(after(pin), "h' :") }, text: { g: after(pin) }, say: "Second case: the rule writes a value its left-hand side pins, here `z`. `valueAt_spec` says the result has that value there, so `v` is `z`. Cost: " + kHb(heartbeats(th)) + " thousand heartbeats." },
      ],
    },
    {
      id: 'p12',
      title: 'Witnesses that the statements are not empty',
      panes: [
        { id: 's', label: 'The witnesses', source: props },
        { id: 't', label: 'Steps and stuckness, computed', source: stepOf },
        { id: 'p', label: 'Their proofs', source: proofs },
      ],
      frames: [
        {
          say: "Here's the trap. An invariant `∀ x y, Step x y → P x → P y` is true for every `P` if `Step` relates nothing, and true for a given `P` if `P` holds of every configuration. Determinism is true if `Step` relates nothing. Without more, these could all be ==true for an empty reason==.",
          ask: {
            q: "Which witness rules out a `Step` that relates every configuration to something?",
            options: ["`step_run_succ`", "`stuck_done`: the configuration `done(z)` has no successor", "`doneHoldsZero_fails`"],
            answer: 1,
            why: "The other witnesses rule out the opposite failures: `Step` relating nothing, and an invariant that holds of everything.",
          },
        },
        { hl: { s: span(props, 'def step_run_succ.statement', '∃ x y : Config, x.val = cfg (run (s z)) ctr0') }, notes: [note('s', lineOf(props, 'def step_run_succ.statement'), "There are configurations `run(s(z))` and `run(z)`, with the counter of the initial configuration, and a step between them.")] },
        { hl: { t: [...span(stepOf, 'noncomputable def stepAt', 'c.rules[i]?.bind'), ...span(stepOf, 'theorem step_of', '{x y : Config c} (h : stepAt c i x.val = some y.val)')] }, notes: [note('t', lineOf(stepOf, 'noncomputable def stepAt'), "Computes the successor of a term by one rule: match the left-hand side, evaluate the right-hand side."), note('t', lineOf(stepOf, 'theorem step_of'), "A computed successor is a step.")] },
        { hl: { p: [lineOf(proofs, 'stepAt peanoCore 0 (cfg (run (s z)) ctr0)'), ...span(proofs, 'theorem step_run_succ', 'StepDecide.step_of nd 0')] }, notes: [note('p', lineOf(proofs, 'stepAt peanoCore 0 (cfg (run (s z)) ctr0)'), "`run(s(z))` computes to `run(z)`, as a fact in `checks`.")], say: "The witness also needs each configuration's sort, also from `checks`." },
        { hl: { t: span(stepOf, 'noncomputable def noHead', '(y : Config c) : ¬ Step c x y'), p: span(proofs, 'theorem stuck_done', 'StepDecide.stuck_of') }, notes: [note('t', lineOf(stepOf, 'noncomputable def noHead'), "No rule's left-hand side has the constructor `done(z)` has at the operand position."), note('p', lineOf(proofs, 'theorem stuck_done'), "`stuck_of` turns that into \"no step\".")] },
        { hl: { s: span(props, 'def doneHoldsZero_fails.statement', '∃ x : Config, x.val = cfg (done (natVal (s z))) ctr0'), p: span(proofs, 'theorem doneHoldsZero_fails', 'fun h => checks') }, notes: [note('s', lineOf(props, 'def doneHoldsZero_fails.statement'), "`done(s(z))` is a configuration that does not satisfy the predicate, so the invariant is not true of everything.")] },
      ],
    },
    {
      id: 'p13',
      title: 'What the proofs cost',
      visual: costs,
      frames: [
        { say: "Each declaration's cost, in thousands of ==heartbeats==: Lean's count of small allocations on the elaborating thread, including kernel checking. They don't depend on the machine's speed. They were measured by elaborating the proof file once." },
        { say: "The decision on the data costs most. Everything else is a few applications of lemmas proved once." },
        { say: "The whole file, including the definitions of `PeanoChecks` and small helper facts, costs " + kHb(allHb) + " thousand heartbeats." },
        { say: "None of these numbers is in a statement. Lesson 7 shows how an unattended loop brought them here, judged only by the kernel." },
      ],
    },
  ],
  quiz: [
    {
      q: "What does a statement of the form `∀ x y, Step x y → P x → P y` say if `Step` relates nothing?",
      options: ["It is false", "Nothing: it holds for every `P`", "It holds only for true `P`"],
      answer: 1,
      why: "It also holds trivially if `P` is true of every configuration. The witnesses exclude both.",
    },
    {
      q: "Why one decision for all the facts, not one per fact?",
      options: ["Lean allows only one `decide` per file", "The kernel evaluates many of them through the same lookups in peano's data, and in one decision that work is shared", "It reads better"],
      answer: 1,
      why: "The loop of lesson 7 found that merging them was cheaper.",
    },
    {
      q: "Does `deterministic_of` cover every deterministic definition?",
      options: ["Yes", "No: some are deterministic for reasons other than distinct constructors at one position", "Only peano"],
      answer: 1,
      why: "For those a different theorem is needed. The statement stays the same.",
    },
    {
      q: "Can a cheaper proof make a statement weaker?",
      options: ["Yes, that's the usual trade-off", "No: the statement is a fixed definition, and the kernel checks any new proof against it"],
      answer: 1,
      why: "A loop changes proofs and lemmas only.",
    },
    {
      q: "Is the value of `pred(s(N))` unique, or could `Eval` give it two values?",
      options: ["Unique, by the generic theorem `Eval.det`, proved once with no hypothesis", "It could give two if `N` is not a `Nat`", "Unique only for peano"],
      answer: 0,
      why: "The first matching clause is determined by the arguments.",
    },
  ],
  checked: [
    "All nine theorems (five properties and four witnesses) are checked by the kernel and use only `propext`, `Classical.choice` and `Quot.sound`. The build pins each one's axiom list, so a new axiom or a `sorry` fails it.",
    "The generic theorems they use (`deterministic_of`, `counter_preserved_of`, `step_of`, `stuck_of`, `valueAt_spec`, `Eval.det`) are kernel-checked once, for every definition.",
    "None of the proofs is reviewed: the kernel checks each against its statement.",
  ],
  tryit: [
    { say: "In the kcore-spec package directory:", cmd: "lake build                                      # includes PeanoProofs and LibraryChecks\nlake env lean KcoreSpec/LibraryChecks.lean      # prints nothing when every axiom list is as pinned" },
    { say: "To see a goal state, open `KcoreSpec/PeanoProofs.lean` in an editor with the Lean extension and place the cursor after a tactic; or add `trace_state` after it and run `lake env lean KcoreSpec/PeanoProofs.lean`. The goals here were printed by Lean's own pretty printer, from the elaborator's info trees, without editing the file." },
  ],
}
