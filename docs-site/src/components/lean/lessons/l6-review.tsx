'use client'

// Lesson 6: the trusted base, the review cone computed by #review_cone (its output is in the data
// as written), the lines read once and per project, and the differential runs against the reference
// kompile and the K backends.

import type { ReactNode } from 'react'

import { type ConeDecl, config, fmt, groundText, kItem, lean, lineOf, source, span, textSource } from '../data'
import { type Frame, type Lesson, note } from '../lesson'
import { coneNumbers, diffNumbers, initCount, numbers, once, perProject, user } from '../numbers'
import { Bar, Board, Chips, Rows, Small, TextBox } from '../viz'

const coneText = textSource('i-user-core.txt (written by #review_cone)', user.raw)
const checks = source('LibraryChecks')

// ---- trusted, checked, read ------------------------------------------------------------------

const trustColumns: { title: string; items: { key: string; text: ReactNode }[] }[] = [
  {
    title: 'Trusted',
    items: [
      { key: 'kernel', text: <>the Lean {lean.provenance.leanVersion} kernel</> },
      { key: 'axioms', text: <>three axioms: <code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code></> },
      { key: 'init', text: <>{initCount} declarations of Lean's <code>Init</code></> },
      { key: 'kompile', text: <>kompile (krust): the KORE is K's meaning of peano.k</> },
      { key: 'reader', text: <>the KORE reader, for the second route of the per-project check</> },
      { key: 'cone', text: <><code>#review_cone</code> lists everything the statements reach</> },
    ],
  },
  {
    title: 'Checked by the kernel',
    items: [
      { key: 'proofs', text: 'every proof' },
      { key: 'tactics', text: <>tactics and generic lemmas, such as <code>deterministic_of</code>: they only produce proofs</> },
      { key: 'exec', text: <>the executable step, tied to <code>Step</code> by <code>step_iff</code></> },
      { key: 'decisions', text: <>decisions on the data, such as peano's <code>checks</code> and <code>evalReady</code></> },
    ],
  },
  {
    title: 'Read',
    items: [
      { key: 'statements', text: 'the statements' },
      { key: 'deps', text: <>everything they depend on: {coneNumbers.total} lines</> },
    ],
  },
]
const trustLit: string[][] = [[], ['kernel'], ['axioms'], ['init'], ['kompile', 'reader'], ['cone'], ['proofs', 'tactics', 'exec', 'decisions'], ['statements', 'deps']]

// ---- the cone ----------------------------------------------------------------------------------

function declLine(decl: ConeDecl): number {
  const rows = coneText.text.split('\n')
  const i = rows.findIndex((row) => {
    const cells = row.trim().split(/\s+/)
    return cells[0] === `${decl.start}-${decl.end}` && cells[2] === decl.name
  })
  if (i < 0) throw new Error(`lean lessons: the cone listing has no line for ${decl.name}`)
  return i + 1
}

const maxDepth = Math.max(...user.decls.map((d) => d.depth))
const depths = Array.from({ length: maxDepth + 1 }, (_, d) => d)
const coneModules = user.modules
const linesUpTo = (module: string, depth: number) => {
  const covered = new Set<number>()
  for (const d of user.decls) if (d.module === module && d.depth <= depth) for (let l = d.start; l <= d.end; l += 1) covered.add(l)
  return covered.size
}
const namesAt = (depth: number) => user.decls.filter((d) => d.depth === depth).map((d) => d.name.split('.').pop()!)
const sayDepth = (depth: number): string => {
  const here = namesAt(depth)
  if (depth === 0) return 'The roots are the statements and witnesses, ' + here.length + ' definitions. The tool starts from them.'
  const sample = here.slice(0, 4).map((n) => '`' + n + '`').join(', ')
  return 'Through types and values, ' + here.length + ' more declaration' + (here.length > 1 ? 's' : '') + ' at distance ' + depth + ': ' + sample + (here.length > 4 ? ', …' : '')
}
const coneFrames: (Frame & { depth: number })[] = [
  { say: 'The set of declarations a statement depends on is computed by a Lean command, `#review_cone`. It follows the types of reached declarations and the values of reached definitions, ==does not enter proofs==, and stops at Lean\'s own `Init`, `Std` and `Lean`.', depth: -1, hl: { c: [1, 2, 3] } },
  ...depths.map((d) => ({ say: sayDepth(d), depth: d, hl: { c: user.decls.filter((x) => x.depth === d).map(declLine) }, ms: 2200 })),
  { say: 'It ends at ' + coneNumbers.total + ' source lines in ' + coneNumbers.decls + ' declarations, met no theorem (' + coneNumbers.theoremsMet + '), and folded ' + coneNumbers.folded + ' generated declarations into their parents.', depth: maxDepth, hl: { c: span(coneText, '## lines per module', '  298') } },
  {
    say: 'Of these, ==' + coneNumbers.once + ' lines== in five files are the meaning of every K definition, and ' + coneNumbers.perProject + ' lines are peano\'s.',
    depth: maxDepth,
    hl: { c: span(coneText, '## lines per module', '  298') },
    ask: {
      q: 'How can you bound the cone without trusting the tool?',
      options: ['You can\'t: the tool is trusted', 'The eight modules it reaches import only Lean\'s `Init` and each other, so everything the statements can mention is in those files or in `Init`', 'Run it twice'],
      answer: 1,
      why: 'Those files have ' + coneNumbers.files + ' lines. It is a coarser bound, and it costs no trust in the command.',
    },
  },
]
const coneViz = (at: number) => {
  const depth = coneFrames[at].depth
  return (
    <Rows
      head={['Module', { text: 'lines reached', num: true }, { text: '', bar: true }, 'read']}
      rows={coneModules.map((m) => {
        const reached = depth < 0 ? 0 : linesUpTo(m.module, depth)
        return {
          key: m.module,
          state: reached ? undefined : 'faded',
          cells: [m.module.replace('KcoreSpec.', ''), `${reached} / ${m.lines}`, <Bar key="b" pct={(reached / m.lines) * 100} title={`${m.module}: ${reached} of ${m.lines} lines`} />, <Small key="s">{once.includes(m.module) ? 'once' : 'per project'}</Small>],
        }
      })}
      foot={['total', `${depth < 0 ? 0 : coneModules.reduce((s, m) => s + linesUpTo(m.module, depth), 0)} / ${coneNumbers.total}`, '', '']}
    />
  )
}

// ---- what to read ------------------------------------------------------------------------------

const files: Record<string, string> = {
  'KcoreSpec.FixedSignature': 'FixedSignature', 'KcoreSpec.Core': 'Core', 'KcoreSpec.Value': 'Value', 'KcoreSpec.Evaluation': 'Evaluation',
  'KcoreSpec.Step': 'Step', 'KcoreSpec.PeanoCore': 'PeanoCore', 'KcoreSpec.PeanoLibrary': 'PeanoLibrary', 'KcoreSpec.PeanoProperties': 'PeanoProperties',
}
const questionOf: Record<string, string> = {
  'KcoreSpec.FixedSignature': "Which sorts and constructors does every kompiled definition have before the user's: the K sequence, the generated cells, the builtin sorts?",
  'KcoreSpec.Core': "What is a definition's content: sorts, constructors, subsorts, functions as ordered clauses with an optional catch-all, rules between configurations?",
  'KcoreSpec.Value': "What is a configuration: a ground term whose computed sort is the configuration sort?",
  'KcoreSpec.Evaluation': "What does it mean for a pattern to match, and what value does a function or a right-hand side have?",
  'KcoreSpec.Step': "What is one rewrite step?",
  'KcoreSpec.PeanoCore': "Is this data peano.k? Read it against the source, or rely on the kernel-checked equality of its emitted KORE with kompile's.",
  'KcoreSpec.PeanoLibrary': "Are the names abbreviations of the right terms, with the labels of the data?",
  'KcoreSpec.PeanoProperties': "Do the statements say what you want?",
}
const order = [...once, ...perProject]
const rangeLines = (m: string) => user.decls.filter((d) => d.module === m).flatMap((d) => Array.from({ length: d.end - d.start + 1 }, (_, i) => d.start + i))
const readFrames: Frame[] = order.map((m) => ({
  say: '`' + files[m] + '.lean`, ' + user.totals[m].coneLines + ' of ' + user.totals[m].fileLines + ' lines.',
  text: { f: source(files[m]) },
  hl: { f: rangeLines(m) },
  notes: [note('f', Math.min(...rangeLines(m)), questionOf[m])],
}))
const fileChips = order.map((m) => ({ key: m, text: <>{files[m]} <Small>{user.totals[m].coneLines}</Small></> }))
const readViz = (at: number) => (
  <div>
    <Small>{once.includes(order[at]) ? `Read once: ${coneNumbers.once} lines, ${coneNumbers.onceDecls} declarations` : `Read per project: ${coneNumbers.perProject} lines, ${coneNumbers.perProjectDecls} declarations`}</Small>
    <div style={{ height: 6 }} />
    <Chips items={fileChips} lit={[order[at]]} />
  </div>
)

const evaluation = source('Evaluation')
const step = source('Step')
const value = source('Value')

// ---- the two routes -----------------------------------------------------------------------------

const routes = [
  {
    title: 'Route 1: read it',
    items: [
      { key: 'r1a', text: <>read the data against <code>peano.k</code>, as lesson 4 did</> },
      { key: 'r1b', text: <>needs a reader who knows how kompile compiles K: as-patterns are its sharing of a matched subterm, the counter-cell variable and the injections are its own</> },
    ],
  },
  {
    title: 'Route 2: rely on the kernel',
    items: [
      { key: 'r2a', text: <>kernel evaluation proves the definition well formed, the KORE from data and presentation exactly the syntax tree of kompile's output, and that KORE in the supported fragment</> },
      { key: 'r2b', text: <>every sentence is fixed text or generated from a field of the data, so its rules and equations are the data's</> },
      { key: 'r2c', text: <>the cost moves to reviewing the generator once: its cone is {numbers.emit} lines</> },
      { key: 'r2d', text: <>the kernel check is heavy: last run {numbers.f0Seconds} seconds, {numbers.f0Gb} GiB</> },
    ],
  },
]

// ---- the differentials ---------------------------------------------------------------------------

const refSem = source('refSem')
const parse = source('parseRefSem')
const stepOn = source('stepOnRefSem')
const stepOnRef = source('stepOnRef')
const fixed = source('FixedSignature')
const kc = config('kconfig')
if (kc.sort !== 'GeneratedTopCell' || (kc.successors ?? [null]).length !== 0) throw new Error('lean lessons: the #KConfigValue configuration is no longer a stuck configuration')

const described: { starts: string; text: ReactNode; read: ReactNode }[] = [
  { starts: 'krust only: the constructor `#KConfigValue', text: <>krust only: the constructor <code>#KConfigValue : K → KItem</code> and the function <code>#unboxKConfigValue</code></>, read: 'yes: the constructor' },
  { starts: 'krust only: 16 selector-domain axioms', text: <>krust only: 16 selector-domain axioms and 16 selector-inverse simplification axioms</>, read: 'no (the theory only)' },
  { starts: '`initKCell`', text: <>the equation of <code>initKCell</code>, the initial k cell</>, read: 'no' },
  { starts: 'the no-junk axioms', text: <>no-junk axioms of <code>KItem</code>, <code>Nat</code>, <code>State</code>: order and bound-variable names</>, read: 'no (the theory only)' },
  { starts: 'the no-confusion axioms', text: <>no-confusion axioms of <code>Nat</code> and <code>State</code>: argument order</>, read: 'no (the theory only)' },
  { starts: '8 `isS`', text: <>8 generated <code>isS</code> equations: a bound variable's name</>, read: 'no' },
  { starts: 'attributes: `Source`', text: <><code>Source</code> attributes of builtin sentences</>, read: 'no' },
  { starts: 'attributes: `Location`', text: <><code>Location</code> attributes: starting columns</>, read: 'no' },
  { starts: 'order of the sentences', text: <>order of the sentences, user sorts and constructors</>, read: <>no (proved: <code>stepOn_refSem</code>)</> },
]
const recorded = lean.refKompile.rows
if (recorded.length !== described.length || recorded.some((row, i) => !row.difference.startsWith(described[i].starts))) {
  throw new Error('lean lessons: the reference-kompile differences no longer match the scene’s descriptions')
}
const diffRows = recorded.map((row, i) => ({ ...described[i], sentences: row.sentences }))
const diffFocus: (number[] | null)[] = [null, [0], [0], diffRows.map((_, i) => i).slice(1)]
const diffViz = (at: number) => (
  <>
    <Rows
      head={['Difference (krust against reference)', { text: 'sentences', num: true }, 'read by Step?']}
      rows={diffRows.map((row, i) => ({
        key: String(i),
        state: diffFocus[at] === null ? undefined : diffFocus[at]!.includes(i) ? 'cur' : 'faded',
        cells: [<span key="t" style={{ fontFamily: 'var(--f-sans)' }}>{row.text}</span>, row.sentences, <span key="r" style={{ fontFamily: 'var(--f-sans)' }}>{row.read}</span>],
      }))}
    />
    {(at === 1 || at === 2) && (
      <TextBox label="a configuration of the fixed signature, computed by Lean">
        {groundText(kc.term)}
        <br />
        <Small>k item: <code>{groundText(kItem(kc.term))}</code> · sort: <code>{kc.sort}</code> · successors: {kc.successors?.length}</Small>
      </TextBox>
    )}
  </>
)

const execRows = lean.diff21
const execSum = (k: 'compared' | 'transitions' | 'branching' | 'differences' | 'errors' | 'refSampled' | 'refAgree') => execRows.reduce((t, r) => t + r[k], 0)
const subjectNames: Record<string, string> = { pe: 'peano', rw: 'rewrite.k', bs: 'bounded search', br: 'branching', ow: 'owise competitors', sub: 'subsorts' }
const execViz = (at: number) => (
  <Rows
    head={['definition', { text: 'configurations', num: true }, { text: 'steps', num: true }, { text: 'branching', num: true }, { text: 'differences (krust)', num: true }, { text: 'reference: agree / sampled', num: true }]}
    rows={execRows.map((r) => ({
      key: r.subject,
      state: at === 2 ? (r.branching > 0 ? 'cur' : 'faded') : undefined,
      cells: [subjectNames[r.subject] ?? `synthetic, ${r.subject.replace('syn', '')} rules`, fmt(r.compared), fmt(r.transitions), fmt(r.branching), r.differences + r.errors, `${r.refAgree} / ${r.refSampled}`],
    }))}
    foot={['total', fmt(execSum('compared')), fmt(execSum('transitions')), fmt(execSum('branching')), execSum('differences') + execSum('errors'), `${fmt(execSum('refAgree'))} / ${fmt(execSum('refSampled'))}`]}
  />
)

export const lesson6: Lesson = {
  id: 'what-you-have-to-read',
  number: 6,
  title: 'What you have to read',
  scenes: [
    {
      id: 'r1',
      title: 'Trusted, checked, read',
      visual: (at) => <Board columns={trustColumns} lit={trustLit[at]} />,
      arrange: 'top',
      panes: [{ id: 'c', label: 'The axioms, pinned', source: checks }],
      frames: [
        { say: "Lesson 5 ended with nine theorems the kernel accepted. A skeptical reader still has a question: how do you know the proved statements are about the semantics of `peano.k`, and say what you wanted? A proof is only as good as its statement. Everything here is in one of ==three places==." },
        { say: "The kernel is trusted to check that a proof proves its statement. No `native_decide` is used: every computation in a proof is kernel evaluation." },
        { hl: { c: span(checks, "info: 'KCore.Peano.Ground.deterministic' depends on axioms", '#print axioms KCore.Peano.Ground.counter_preserved') }, notes: [note('c', lineOf(checks, "info: 'KCore.Peano.Ground.deterministic' depends on axioms"), "Only three axioms, and the build fails if another appears: `#print axioms` is pinned per theorem.")] },
        { say: "The statements reach " + initCount + " declarations of Lean's own library, such as `List.find?` and `String`'s order. They are trusted with Lean." },
        { say: "kompile is trusted to produce K's meaning of peano.k, because the semantics here reads KORE-level rules and equations." },
        { say: "`#review_cone` is trusted to be complete, and you'll see a bound that does not trust it." },
        {
          say: "Proofs, tactics, the executable step and the decisions are ==checked, not read==. If any were wrong, a proof would fail to check. It would not prove a different statement.",
          ask: {
            q: "Why can a bug in a tactic or a generic lemma not make a wrong statement true?",
            options: ["Tactics are reviewed carefully", "A tactic only builds a proof term, which the kernel then checks against the statement", "Because Lean has no bugs"],
            answer: 1,
            why: "A wrong tactic fails to produce a proof that checks. It cannot change what the statement says.",
          },
        },
        { say: "What's left to read is the statements and what their meaning depends on: " + coneNumbers.total + " lines, ==computed by Lean==, not chosen by hand." },
      ],
    },
    {
      id: 'r2',
      title: 'Computing what the statements depend on',
      visual: coneViz,
      panes: [{ id: 'c', label: 'The cone, as written', source: coneText, lang: 'none' }],
      frames: coneFrames,
    },
    {
      id: 'r3',
      title: coneNumbers.once + ' lines once, ' + coneNumbers.perProject + ' per project',
      visual: readViz,
      arrange: 'top',
      panes: [{ id: 'f', label: 'What to read', source: source(files[order[0]]) }],
      frames: readFrames,
    },
    {
      id: 'r4',
      title: 'What to check against K while reading',
      panes: [{ id: 'f', label: 'What you are reading', source: evaluation }],
      frames: [
        { text: { f: evaluation }, hl: { f: [lineOf(evaluation, '| .var i, v => some [(i, v)]')] }, notes: [note('f', lineOf(evaluation, '| .var i, v => some [(i, v)]'), "No sort check here. For a well-sorted rule this is sorted matching, because in a well-sorted term every position's sort is fixed by its context.")] },
        { text: { f: evaluation }, hl: { f: [lineOf(evaluation, "(hpre : ∀ cl' ∈ pre, matchTerms c cl'.pats vs = none)")] }, notes: [note('f', lineOf(evaluation, "(hpre : ∀ cl' ∈ pre, matchTerms c cl'.pats vs = none)"), "If two clauses could both match, K's meaning would be the conjunction of two equations. The well-formedness check rules overlapping clauses out, so at most one matches and their order does not matter.")], say: "The evaluation takes the first matching clause." },
        { text: { f: step }, hl: { f: [lineOf(step, '(hmatch : matchTerm c r.lhs x.val = some σ)')] }, notes: [note('f', lineOf(step, '(hmatch : matchTerm c r.lhs x.val = some σ)'), "A step rewrites the whole configuration, because kompile has already turned each rule into one on the whole configuration.")] },
        { text: { f: value }, hl: { f: [lineOf(value, '| dv (s : String) (lit : String)')] }, notes: [note('f', lineOf(value, '| dv (s : String) (lit : String)'), "Any literal is a domain value of a builtin sort, so the configurations are a superset of K's, and a statement over all of them covers K's.")] },
      ],
    },
    {
      id: 'r5',
      title: "Per project: is the data peano.k?",
      visual: (at) => <Board big columns={routes} lit={[['Route 1: read it'], ['Route 2: rely on the kernel'], ['r2c', 'r2d']][at]} />,
      frames: [
        { say: "The " + coneNumbers.perProject + " per-project lines are peano's data (" + numbers.module('PeanoCore') + "), its names (" + numbers.module('PeanoLibrary') + ") and its statements (" + numbers.module('PeanoProperties') + "). For the names, check that each label is the one in the data and the configuration shape is the one in the rules. For the data there are ==two routes==, and either suffices. The first is to read it." },
        { say: "The second is to rely on the kernel, using the round trip of lesson 3." },
        { say: "That trades reading the data for reading the generator, once. It isn't free: the check takes minutes and gigabytes, and it's outside the default build." },
      ],
    },
    {
      id: 'r6',
      title: 'The reference kompile, on the same peano.k',
      panes: [
        { id: 'r', label: 'What parse reads from the reference KORE', source: refSem },
        { id: 'p', label: 'Kernel-checked', source: parse },
      ],
      frames: [
        { say: "The trusted kompile is krust's. To learn whether that choice matters for peano, the reference K kompile (7.1.337, Haskell backend) was run once on the same `peano.k`, and its output compared. This is evidence about krust's output, ==not a reason anything here is correct==: kompile stays in the trusted list." },
        { hl: { r: span(refSem, 'def refSem', '⟨"Lbls", ["Nat"], "Nat"⟩'), p: [lineOf(parse, 'theorem parse_ref_sem'), lineOf(parse, 'theorem wf_parse_ref')] }, notes: [note('r', lineOf(refSem, 'def refSem'), "`peanoCore`, with sorts and constructors declared in another order."), note('p', lineOf(parse, 'theorem parse_ref_sem'), "`parse` accepts the reference KORE, and this is the core it reads.")] },
      ],
    },
    {
      id: 'r7',
      title: 'Both cores have the same step',
      panes: [
        { id: 's', label: 'The step of a core, on ground terms', source: stepOn },
        { id: 'q', label: 'The same step, kernel-checked', source: stepOnRef },
      ],
      frames: [
        { hl: { q: [lineOf(stepOnRef, 'theorem stepOn_refSem')], s: span(stepOn, 'def StepOn', '∃ (hx : c.sortOf x') }, notes: [note('q', lineOf(stepOnRef, 'theorem stepOn_refSem'), "The kernel proves that the two cores have the same step.")], say: "It follows from a generic theorem about cores that agree on what the step reads." },
      ],
    },
    {
      id: 'r8',
      title: 'What actually differs',
      visual: diffViz,
      arrange: 'top',
      panes: [{ id: 'f', label: 'The fixed signature', source: fixed }],
      frames: [
        { say: "The reference KORE is not in the fragment: `emit` does not give it back. In the user module krust has " + lean.refKompile.krustSentences + " sentences, the reference " + lean.refKompile.refSentences + "." },
        { hl: { f: [lineOf(fixed, "Lbl'Hash'KConfigValue")] }, say: "Of the differences, the step reads ==one==: krust adds the constructor `#KConfigValue : K → KItem`, and the fixed signature has it. So configurations include terms the reference signature lacks. For one of them Lean computes the sort `" + kc.sort + "` and no successor." },
        {
          say: "No rule's left-hand side matches such a k cell, and no right-hand side builds one (checked by reading the two rules). A statement about every configuration has to hold for those too. For peano they are stuck, so every statement of lesson 5 holds for them trivially.",
          ask: {
            q: "Does agreement with the reference kompile show that the semantics is right?",
            options: ["Yes, the reference is the definition of K", "No: it is evidence about krust's output on one definition", "Yes, for all definitions"],
            answer: 1,
            why: "kompile stays in the trusted list. What is proved is that the two outputs give the same step on peano.",
          },
        },
        { say: "The other differences are axioms of the theory, presentation and order. The step reads none of them." },
      ],
    },
    {
      id: 'r9',
      title: 'The step against two K backends',
      visual: execViz,
      frames: [
        { say: "That differential was about kompile's output. A second one is about the step. The package's executable step, which lesson 4 proves equal to `Step`, was compared with krust's own execution of the same KORE, one step at a time." },
        { say: "Each row is a definition in the fragment: corpus examples and a synthetic family with " + execRows.filter((r) => r.subject.startsWith('syn')).map((r) => r.subject.replace('syn', '')).join(', ') + " rules. The configurations are every one reachable from many small programs, and generated ones no program reaches." },
        { say: "Some configurations have more than one successor (" + fmt(execSum('branching')) + " of them). The comparison is of the whole set of successors." },
        { say: "Differences between the two sets, on " + fmt(execSum('compared')) + " configurations: " + execSum('differences') + ". Errors from either side: " + execSum('errors') + "." },
        { say: "A sample was also run through the reference K backend: " + fmt(execSum('refAgree')) + " of " + fmt(execSum('refSampled')) + " agree." },
        {
          say: "This is ==evidence== about the step definition, from two implementations written independently of it. It isn't a proof. The proof that the step is K's meaning its soundness and completeness, lesson 8.",
          ask: {
            q: "What could make both backends and the package agree and all be wrong?",
            options: ["Nothing: three independent agreements prove it", "A misreading of K shared by all three, or a difference outside what was tested, such as terms deeper than the enumeration or k cells with more than two items", "A bug in the differential's output format only"],
            answer: 1,
            why: "Agreement makes a shared mistake less likely, and a disagreement would point at a configuration to reason about. Neither is a reason for correctness.",
          },
        },
        { say: "The same comparison was run for the second fragment, F1, on definitions with several cells, Int, Bool and maps. [Lesson 9](/lean/beyond-peano) has it." },
      ],
    },
    {
      id: 'r10',
      title: 'Not per project: soundness and completeness',
      panes: [{ id: 't', label: 'Stated, not proved', source: source('soundAndComplete') }],
      frames: [
        { say: "The statements of the matching-logic track, which say the reference step is sound and complete for the theory of the KORE text, are reviewed once and separately. Their cone is " + numbers.rootText + " lines: the matching-logic patterns and semantics, the KORE syntax, the translation of KORE into matching logic, and the generator." },
        { hl: { t: [lineOf(source('soundAndComplete'), 'theorem sound_and_complete')] }, notes: [note('t', lineOf(source('soundAndComplete'), 'theorem sound_and_complete'), "Stated, not proved.", 'sorry')], say: "No per-project statement depends on it. Lesson 8 covers it." },
      ],
    },
  ],
  quiz: [
    {
      q: "Why does the cone not enter proofs?",
      options: ["It would take too long", "A proof can only prove the statement it is checked against, so its content cannot change what the statement means", "Proofs are not stored in Lean"],
      answer: 1,
      why: "Subterms whose type is a proposition are skipped, and theorems other than the roots are not entered.",
    },
    {
      q: "Why can a reader skip `DecidableEq` of ground terms, which proofs use constantly?",
      options: ["It's derived, so it must be right", "No statement mentions it: it lives in `Execution.lean`, outside the cone, and is used only inside proofs, which the kernel checks", "It is trusted with Lean"],
      answer: 1,
      why: "Being used a lot in proofs doesn't put something in the reader's path.",
    },
    {
      q: "What changes for a second definition?",
      options: ["Everything has to be read again", "Only the per-project part: its data, its names and its statements", "Nothing"],
      answer: 1,
      why: "The " + coneNumbers.once + " lines of the shared files are read once.",
    },
    {
      q: "Which row of the trusted list does the reference differential bear on?",
      options: ["The Lean kernel", "kompile's", "`#review_cone`"],
      answer: 1,
      why: "The differential is evidence about krust's output, not a reason anything is correct. The row stays trusted.",
    },
    {
      q: "Why does a statement over all configurations still say something about the reference's configurations?",
      options: ["The two kompiles have the same configurations", "The reference's configurations are among them, since its signature has fewer constructors", "It doesn't"],
      answer: 1,
      why: "And the extra ones are stuck and unreachable from peano's. A statement for all configurations is in particular a statement for the reference's.",
    },
  ],
  checked: [
    "The cone listings are the output of `#review_cone` at the recorded commit; the scene shows the file as written. An upper bound that doesn't trust the command: the eight modules it reaches import only `Init` and each other.",
    "That the Lean data is peano's KORE: kernel-checked (the second route), in a long run.",
    "The differential: `parse` accepting the reference KORE, its core being peano's up to declaration order, the same step relation, and the reference KORE being outside the fragment are kernel decisions. That the extra configurations are stuck and unreachable for peano was checked by reading the two rules; the scene also shows Lean computing that one of them has no successor.",
    "The execution differential: run outside Lean, by a harness that evaluates the package's step and calls krust and the reference backend. Its numbers (" + diffNumbers.configs + " configurations) are the harness's summary. Evidence, not proof.",
    "Trusted: the items in the first scene.",
  ],
  tryit: [
    { say: "In the kcore-spec package directory:", cmd: "lake build                           # the library and its checks\nlake env lean test/ReviewCone.lean   # about 3 s; writes the three cone listings\nlake env lean test/F0Check.lean      # heavy: the kernel checks of the second route" },
    { say: "The last line is heavy: its last run took " + numbers.f0Minutes + " minutes and " + numbers.f0Gb + " GiB of memory. To review another definition, list its statement definitions as the roots of a new `#review_cone` line in `test/ReviewCone.lean`." },
  ],
}
