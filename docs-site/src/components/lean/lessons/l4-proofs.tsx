'use client'

// Lesson 4: peano's nine statements and their proofs over the generated package. Determinism and
// the counter cell come from the package's generated theorems, each a generic theorem applied to
// one kernel decision; the rest are the user's, with a run certificate. Every pane is a file of the
// package or of the user's package, or an excerpt of KCore's generic theorems.

import { build, lean, lineOf, slice, source, span } from '../data'
import { type Lesson, note } from '../lesson'
import { Rows } from '../viz'

const stmts = slice(source('userStatements'), '@[match_pattern, reducible] def z', 'def counter_preserved.statement')
const proofs = slice(source('userProofs'), 'theorem deterministic\'', 'end Peano')
const ufacts = slice(source('userFacts'), 'theorem sorted_runSZ', 'theorem guardDone')
const cert = slice(source('userCert'), 'def runs', 'theorem peano_reaches')
const det = slice(source('pkgDet'), '/-- **The definition is deterministic.** -/', '  Det.deterministic_of')
const detIndex = slice(source('pkgDetIndex'), 'det_index_of ix', 'theorem idx_ok')
const counter = slice(source('pkgCounter'), '/-- The rules whose step may change', '  steps_of (frame_sound counterPath)')
const detOf = source('detOf')
const apart = source('apart')
const stepsOf = source('stepsOf')
const frameOK = source('frameOK')
const checkRun = source('checkRunSound')
const krustRun = source('certTerm')

const statementNames = [...source('userStatements').text.matchAll(/^def (\w+)\.statement/gm)].map((m) => m[1])
const proved = statementNames.filter((n) => new RegExp(`^theorem ${n}'? : ${n}\\.statement`, 'm').test(source('userProofs').text))
if (statementNames.length !== 9 || proved.length !== 9) throw new Error(`lean lessons: peano has ${statementNames.length} statements, ${proved.length} proved`)
if (!source('pkgCounter').text.includes('def counterObl : List Nat := []') || !source('pkgDetIndex').text.includes('def ovl : List (Nat × Nat) := []')) {
  throw new Error('lean lessons: peano now has obligations or overlaps')
}

const userCost = () => (
  <Rows
    head={['Your module', { text: 'seconds', num: true }, { text: 'peak GB', num: true }]}
    rows={['User.Statements', 'User.Facts', 'User.Proofs', 'User.Cert'].map((m) => ({ key: m, cells: [m, build(m).seconds.toFixed(1), (build(m).rssMiB / 1024).toFixed(1)] }))}
  />
)

export const lesson4: Lesson = {
  id: 'proving-peanos-claims',
  number: 4,
  title: "Proving peano's claims",
  scenes: [
    {
      id: 'q1',
      title: 'The statements',
      panes: [{ id: 's', label: 'User/Statements.lean', source: stmts, lang: 'lean' }],
      frames: [
        { hl: { s: [lineOf(stmts, 'def deterministic.statement'), ...span(stmts, 'def counterIs', 'def counter_preserved.statement')] }, notes: [note('s', lineOf(stmts, 'def deterministic.statement'), '"A configuration has at most one next one."', 'deterministic.statement'), note('s', lineOf(stmts, 'def counter_preserved.statement'), '"The counter cell never changes."', 'counter_preserved.statement')], say: `Lesson 1 ended with two claims about every configuration. Here they are as Lean statements, in your package, with ${statementNames.length - 2} more.` },
        { hl: { s: span(stmts, '@[match_pattern, reducible] def z', 'def ctr0') }, notes: [note('s', lineOf(stmts, '@[match_pattern, reducible] def s'), "Your names for terms, built from the package's numbered symbols.", 'Sym.«s»')] },
        { hl: { s: span(stmts, 'def pred_succ.statement', '∀ N : GroundTerm, c.sortOf N = some Srt.«Nat» → (∀ M, N ≠ s M) → Pred N z') }, notes: [note('s', lineOf(stmts, 'def pred_succ.statement'), "`pred`'s two equations, for every `Nat`.", 'pred_succ.statement')] },
        {
          hl: { s: span(stmts, 'def step_run_succ.statement', '∃ x : Config c, x.val = cfg (done (natVal (s z))) ctr0 ∧ ¬ doneHoldsZero x') },
          notes: [note('s', lineOf(stmts, 'def stuck_done.statement'), 'Particular configurations, and how they step.', 'stuck_done.statement')],
          say: 'Four ==witnesses==. An invariant `∀ x y, Step x y → P x → P y` holds for every `P` if `Step` relates nothing, and determinism holds too. The witnesses rule that out: steps exist, and the invariant can fail.',
        },
        { hl: { s: span(stmts, 'def doneHoldsZero (x', 'def doneHoldsZero_preserved.statement') }, notes: [note('s', lineOf(stmts, 'def doneHoldsZero_preserved.statement'), 'A second invariant: a `done` reached by a step holds `z`.', 'doneHoldsZero_preserved.statement')] },
      ],
    },
    {
      id: 'q2',
      title: 'Determinism, generated',
      panes: [
        { id: 'p', label: 'Peano/Kinds/Det.lean', source: det, lang: 'lean' },
        { id: 't', label: 'KcoreSpec/DetSound.lean', source: detOf, lang: 'lean' },
      ],
      frames: [
        { hl: { p: span(det, 'theorem deterministic', 'Det.deterministic_of') }, notes: [note('p', lineOf(det, 'Det.deterministic_of'), 'One application of a theorem proved once, for every definition.', 'Det.deterministic_of')], say: 'Every proof here has the same shape. A ==generic theorem== reduces the property to a check on the definition\'s data; ==one kernel decision== runs the check on peano; the proof applies the one to the other.' },
        { hl: { t: span(detOf, 'theorem deterministic_of', '{ix : DetIndex} (hd : detOK c T ix = true)') }, notes: [note('t', lineOf(detOf, 'theorem deterministic_of'), "`step_iff`'s three conditions, the tables…", 'hok'), note('t', lineOf(detOf, '(hd : detOK'), '…and the check itself.', 'detOK c T ix = true')] },
        { hl: { t: [lineOf(detOf, "(h : Step c x y) (h' : Step c x y')")] }, notes: [note('t', lineOf(detOf, "(h : Step c x y) (h' : Step c x y')"), 'Two steps from one configuration reach one configuration.', "y = y'")] },
      ],
    },
    {
      id: 'q3',
      title: 'The check: no two rules overlap',
      panes: [
        { id: 'o', label: 'KcoreSpec/Determinism.lean', source: { ...apart }, lang: 'lean' },
        { id: 'i', label: 'Peano/Facts/DetIndex.lean', source: detIndex, lang: 'lean' },
      ],
      frames: [
        { hl: { o: span(apart, 'def apart', '| none => true') }, notes: [note('o', lineOf(apart, '| none => true'), 'The two left-hand sides have no common instance: no configuration matches both.', 'none => true')], say: "Each rule on its own gives one result: its match fixes everything its right-hand side reads. Two rules of one priority could still both apply to a configuration. For peano's pair, the check shows they are ==apart==." },
        { hl: { o: [lineOf(apart, '| some C => clashes')] }, notes: [note('o', lineOf(apart, '| some C => clashes'), 'Or they do, but their `requires` contradict each other.', 'clashes')], say: "peano's rules match `run(s(N))` and `run(z)`. `s` and `z` are different constructors, so no configuration matches both." },
        { hl: { i: [lineOf(detIndex, 'det_index_of ix')] }, notes: [note('i', lineOf(detIndex, 'det_index_of ix'), "The symbol each rule requires at a few positions, computed by the generator.", 'at [[')], say: 'Comparing every pair costs a lot in a large definition. So the check first reads an ==index==: the symbols each rule requires at a few positions. Two rules requiring different symbols at one position are apart, with no further work.' },
        { hl: { i: [lineOf(detIndex, 'def ovl'), lineOf(detIndex, 'theorem idx_ok')] }, notes: [note('i', lineOf(detIndex, 'theorem idx_ok'), "The generator's index is checked, not trusted.", 'decide +kernel'), note('i', lineOf(detIndex, 'def ovl'), 'Pairs the check cannot separate would be listed here, as obligations. peano has none.', ':= []')] },
      ],
    },
    {
      id: 'q4',
      title: 'The counter cell, generated',
      panes: [
        { id: 'c', label: 'Peano/Kinds/Counter.lean', source: counter, lang: 'lean' },
        { id: 'f', label: 'KcoreSpec/Invariant.lean', source: frameOK, lang: 'lean' },
      ],
      frames: [
        { hl: { c: [lineOf(counter, 'theorem counterFrame')] }, notes: [note('c', lineOf(counter, 'theorem counterFrame'), 'Every rule keeps the counter cell: one decision.', 'frameOK c counterPath')] },
        { hl: { f: span(frameOK, 'def frameOK', '| some (.as _ j), some (.var j\') => j == j\'') }, notes: [note('f', lineOf(frameOK, 'def frameOK'), "A rule keeps a position if its left-hand side binds a variable there and its right-hand side has the same variable there.", 'frameOK')], say: 'This is lesson 1\'s observation about `DotVar0`, as a check: variable 2 sits in the counter cell on both sides of each rule.' },
        { hl: { c: [lineOf(counter, 'def counterObl')] }, notes: [note('c', lineOf(counter, 'def counterObl'), 'Rules that may change the cell, such as one that takes a fresh number, would be listed as obligations. peano has none.', ':= []')] },
        { hl: { c: span(counter, 'theorem counter_kept', 'steps_of (frame_sound counterPath)') }, notes: [note('c', lineOf(counter, 'steps_of (frame_sound counterPath)'), "The generic theorem: a decided condition on each rule gives a property of every step.", 'steps_of')] },
      ],
    },
    {
      id: 'q5',
      title: 'Any property of each step',
      panes: [{ id: 's', label: 'KcoreSpec/Invariant.lean', source: stepsOf, lang: 'lean' }],
      frames: [
        { hl: { s: span(stepsOf, 'def RuleSteps', 'EvalTerm c σ r.rhs (some y) → P x y') }, notes: [note('s', lineOf(stepsOf, 'def RuleSteps'), 'Every step by rule r has the property P.', 'def RuleSteps')] },
        { hl: { s: span(stepsOf, 'theorem steps_of', '∀ x y : Config c, Step c x y → P x.val y.val := by') }, notes: [note('s', lineOf(stepsOf, '(sound :'), 'A condition on a rule that gives P…', 'sound'), note('s', lineOf(stepsOf, '(h : allExcept'), '…holding of every rule but the listed ones…', 'allExcept'), note('s', lineOf(stepsOf, '(ho :'), '…which are proved by hand…', 'ho'), note('s', lineOf(stepsOf, '∀ x y : Config c'), '…gives P for every step.', 'Step c x y → P x.val y.val')], say: 'The counter cell is one use. Your package uses the same theorem for `doneHoldsZero`, with a different condition.' },
      ],
    },
    {
      id: 'q6',
      title: 'Your proofs',
      panes: [{ id: 'p', label: 'User/Proofs.lean', source: proofs, lang: 'lean' }],
      frames: [
        { hl: { p: [lineOf(proofs, "theorem deterministic'")] }, notes: [note('p', lineOf(proofs, "theorem deterministic'"), "The generated theorem, as the statement asks for it.", 'deterministic h h\'')] },
        { hl: { p: span(proofs, 'theorem counter_preserved', 'exact (counterIs_iff ctr y.val)') }, notes: [note('p', lineOf(proofs, 'have hf := counter_kept'), 'The generated theorem, with no obligations…', 'counter_kept'), note('p', lineOf(proofs, 'exact (counterIs_iff ctr y.val)'), '…read through a small lemma that says what the statement\'s shape means at the counter\'s position.', 'counterIs_iff')] },
        { hl: { p: span(proofs, 'theorem doneHoldsZero_preserved', 'exact Option.some.inj') }, notes: [note('p', lineOf(proofs, 'have hg := steps_of (guard_sound doneGuard)'), "`steps_of` again, with a condition you chose: after any step, a `done` at the head of the k cell holds `z`.", 'guard_sound doneGuard')] },
        { hl: { p: span(proofs, 'theorem pred_succ', '(.cons (.ctor rfl (.cons (.var rfl) .nil)) .nil)') }, notes: [note('p', lineOf(proofs, '.clause (pre := [])'), "`Eval.clause` of lesson 3, built directly: the clause, σ, and the match.", '.clause')], say: 'The equations of `pred` are proved by building the evaluation itself, with the constructors of lesson 3.' },
      ],
    },
    {
      id: 'q7',
      title: 'Witnesses',
      panes: [
        { id: 'f', label: 'User/Facts.lean', source: ufacts, lang: 'lean' },
        { id: 'p', label: 'User/Proofs.lean', source: proofs, lang: 'lean' },
      ],
      frames: [
        { hl: { f: span(ufacts, 'theorem succ_runSZ', 'decide +kernel') }, notes: [note('f', lineOf(ufacts, 'theorem succ_runSZ'), 'The kernel computes the successors of `run(s(z))` and finds `run(z)` among them.', 'successorsN')], say: 'A witness is a fact about one configuration, so the kernel can compute it.' },
        { hl: { p: span(proofs, 'theorem step_run_succ', '⟨x, ⟨y, hs⟩, rfl') }, notes: [note('p', lineOf(proofs, 'Det.step_of_mem'), 'A listed successor is a `Step`: the direction of `step_iff` that needs no search.', 'step_of_mem')] },
        { hl: { f: span(ufacts, 'theorem nomatch_doneZ', '(Exec.wellSorted c r.vars)).isEmpty) = true := by decide +kernel'), p: [lineOf(proofs, 'theorem stuck_done')] }, notes: [note('f', lineOf(ufacts, 'theorem nomatch_doneZ'), 'No rule matches `done(z)`…', 'nomatch_doneZ'), note('p', lineOf(proofs, 'theorem stuck_done'), '…so, by `step_iff`, it has no step.', 'stuck_of')] },
      ],
    },
    {
      id: 'q8',
      title: 'A run, as a theorem',
      panes: [
        { id: 'c', label: 'User/Cert.lean', source: cert, lang: 'lean' },
        { id: 't', label: 'KcoreSpec/Cert.lean', source: checkRun, lang: 'lean' },
      ],
      visual: (at) => (at === 2 ? userCost() : null),
      frames: [
        { hl: { c: span(cert, 'def runs', 'theorem peano_stuck') }, notes: [note('c', lineOf(cert, 'def runs'), "Lesson 1's run: the rule of each step and the configuration it reaches.", 'runs'), note('c', lineOf(cert, 'theorem peano_run'), 'The kernel replays it.', 'checkRun')], say: "Lesson 1 could only print a run. Here it is a theorem: `run(s(s(z)))` reaches `done(z)` in three steps, and `done(z)` has no successor." },
        { hl: { t: span(checkRun, 'theorem checkRun_sound', 'Reach (Step c)') }, notes: [note('t', lineOf(checkRun, 'Reach (Step c)'), 'A run that checks is a sequence of `Step`s.', 'Reach (Step c)')] },
        { say: `All nine statements and the run take ${(['User.Statements', 'User.Facts', 'User.Proofs', 'User.Cert'] as const).reduce((s, m) => s + build(m).seconds, 0).toFixed(0)} seconds to check, with no per-rule proof.` },
      ],
    },
    {
      id: 'q9',
      title: 'A run krust recorded',
      panes: [{ id: 'k', label: 'Peano/Certs/term.lean', source: krustRun, lang: 'lean' }],
      frames: [
        { say: `You wrote that certificate by hand. The generator writes one for each run krust recorded for the definition. For peano that is a run of ${lean.package.certSteps} steps, and it is part of the generated package.` },
        { hl: { k: span(krustRun, 'theorem term_run', 'checkRun_sound ok srReady matchReady term_run') }, notes: [note('k', lineOf(krustRun, 'theorem term_run'), "The kernel replays krust's steps…", 'checkRun'), note('k', lineOf(krustRun, 'Reach (Step c)'), '…so they are a run of `Step`.', 'Reach (Step c)')] },
        { hl: { k: span(krustRun, 'theorem term_stuck', 'stuckCheck_sound') }, notes: [note('k', lineOf(krustRun, 'theorem term_ends'), 'Where krust stopped, `Step` has no successor either.', 'term_ends')], say: "So each of krust's steps is one `Step` allows, and where krust stopped, no step is left." },
      ],
    },
  ],
  quiz: [
    {
      q: 'Why does peano need four witnesses besides its invariants?',
      options: ['To make the proofs faster', 'An invariant or determinism holds trivially if `Step` relates nothing; the witnesses show steps exist and the invariant can fail', 'Because krust requires them'],
      answer: 1,
      why: 'They rule out a statement that is true for an empty reason.',
    },
    {
      q: 'What would the generator do for a rule that writes a fresh number into the counter cell?',
      options: ['Fail', 'List it in `counterObl`, so `counter_kept` asks you to prove that rule keeps the cell, or you state a weaker property', 'Silently skip it'],
      answer: 1,
      why: 'A rule the decision cannot handle becomes a named obligation of the theorem.',
    },
  ],
  checked: [
    "All nine statements and the run certificate, by the kernel, each proof using only `propext`, `Classical.choice` and `Quot.sound` (`User/Proofs.lean` and `User/Cert.lean` check their axioms when they build).",
    '`deterministic` and `counter_kept`, generated, by the kernel: generic theorems applied to one decision each, with no obligations for peano.',
    `\`term_reaches\` and \`term_ends\`, generated, by the kernel: krust's recorded run of peano, ${lean.package.certSteps} steps, is a run of \`Step\`, and \`Step\` has no step from where it stops.`,
    'The statements are written by hand. Reading them, and the definitions they mention, is your part: a proof of the wrong statement checks just as well.',
  ],
  tryit: [
    {
      say: 'In the kcore-spec package directory, with the library built (`lake build KcoreSpec kcore`), regenerate peano\'s package, build it and your modules:',
      cmd: 'examples/run.sh peano',
    },
  ],
}
