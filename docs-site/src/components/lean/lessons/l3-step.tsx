'use client'

// Lesson 3: what a step of peano is, in KCore's frozen definitions: configurations, matching,
// evaluation, `Step`; then the executable step and `step_iff`. The matches, values and successors
// shown were computed by compiled Lean on KCore's parse of peano's KORE (Facts.lean).

import { type ConfigFact, config, kItem, kText, lean, lineOf, slice, source, span, substText } from '../data'
import { type Lesson, note } from '../lesson'
import { Rows, Svg, Tree, groundTree } from '../viz'

const terms = slice(source('coreTerms'), '/-- A ground value')
const sortOf = source('valueSortOf')
const configDef = source('valueConfig')
const patVal = source('patVal')
const evalTerm = source('evalTerm')
const evalEval = source('evalEval')
const step = source('step')
const successors = source('successors')
const stepIffOk = source('stepIffOk')
const surface = slice(source('pkgSurface'), '/-- The executable step lists exactly', '  Exec.step_iff_of_ok c ok srReady matchReady x y')
const facts = slice(source('pkgFacts'), 'theorem srReady : c.srReady = true', 'theorem matchReady')

const c0 = config('c0')
const c1 = config('c1')
const c2 = config('c2')
const k = (c: ConfigFact) => kText(kItem(c.term))
const only = (c: ConfigFact, rule: number) => {
  const m = c.rules[rule].matches
  if (m.length !== 1 || m[0].applies !== true || !m[0].rhs) throw new Error(`lean lessons: ${c.name} has not one applying match of rule ${rule}`)
  return m[0]
}
const m00 = only(c0, 0)
const m11 = only(c1, 1)
if (c0.rules[1].matches.length !== 0 || c1.rules[0].matches.length !== 0 || c2.rules.some((r) => r.matches.length)) {
  throw new Error('lean lessons: a rule now matches a configuration this lesson says it does not')
}
if (c0.sort !== 'GeneratedTopCell' || k(c0) !== 'run(s(z))' || k(c1) !== 'run(z)') throw new Error('lean lessons: the configurations of lesson 3 changed')
const pred = lean.facts.pred
const predOf = (arg: string) => {
  const found = pred.find((p) => kText(p.arg) === arg)
  if (!found?.value) throw new Error(`lean lessons: no value of pred(${arg})`)
  return kText(found.value)
}

const tree = () => (
  <Svg viewBox="0 0 520 470" label={`The configuration as a tree: ${kText(c0.term)}`}>
    <Tree node={groundTree(c0.term)} x={10} y={30} w={500} dy={60} />
  </Svg>
)

const succRows = (at: number) => (
  <Rows
    head={['Configuration', 'Successors']}
    rows={['c0', 'c1', 'c2', 'c3', 'kconfig'].map((name, i) => {
      const c = config(name)
      return { key: name, cells: [k(c).replace('#KConfigValue(dotk)', '#KConfigValue(.K)'), c.successors.length ? c.successors.map((y) => k({ ...c, term: y })).join(', ') : 'none'], state: at === i ? 'cur' : undefined }
    })}
  />
)

export const lesson3: Lesson = {
  id: 'what-a-step-means',
  number: 3,
  title: 'What a step means',
  scenes: [
    {
      id: 's0',
      title: 'A configuration is a tree',
      visual: tree,
      frames: [
        { say: "`run(s(z))` steps to `run(z)` by peano's first rule. To rely on that, you need to know what a configuration is, when a rule applies, and what its right-hand side evaluates to. Each is a definition in KCore, written once for every definition." },
        { say: "Here is lesson 1's configuration, as a tree: the top cell holds the k cell and the counter cell, and the k cell holds `run(s(z))`, injected into `KItem`." },
      ],
    },
    {
      id: 's1',
      title: 'Trees and their sorts',
      panes: [
        { id: 't', label: 'KcoreSpec/Core.lean', source: terms, lang: 'lean' },
        { id: 'v', label: 'KcoreSpec/Value.lean', source: sortOf, lang: 'lean' },
      ],
      frames: [
        { hl: { t: span(terms, 'inductive GroundTerm where', '| dv (s : Srt) (lit : Lit)') }, notes: [note('t', lineOf(terms, 'inductive GroundTerm where'), 'A tree: constructors applied to arguments, injections between sorts, and literals. Then maps, sets and lists, which peano does not use; maps and sets are kept sorted, so equal values are equal trees.')] },
        { hl: { v: [lineOf(sortOf, 'def sortOf'), lineOf(sortOf, '| .ctor f ts =>')] }, notes: [note('v', lineOf(sortOf, '| .ctor f ts =>'), "A constructor's arguments must have its argument sorts.", '.ctor f ts')], say: "`sortOf` computes a tree's sort from the definition's data, or `none` when the tree is not well sorted." },
      ],
    },
    {
      id: 's1b',
      title: 'Configurations',
      panes: [{ id: 'v', label: 'KcoreSpec/Value.lean', source: configDef, lang: 'lean' }],
      frames: [
        { hl: { v: [lineOf(configDef, 'def Value')] }, notes: [note('v', lineOf(configDef, 'def Value'), 'A value of sort `s`: a tree together with a proof that its sort is `s`.', '{ t : GroundTerm // c.sortOf t = some s }')] },
        { hl: { v: [lineOf(configDef, 'abbrev Config')] }, notes: [note('v', lineOf(configDef, 'abbrev Config'), 'A configuration: a value of the top cell\'s sort.', 'topCellSort')], say: `Lean computes the sort of lesson 1's tree as \`${c0.sort}\`, the top cell's, so it is a configuration. Statements quantify over \`Config\`, so they range over every well-sorted configuration, reachable or not.` },
      ],
    },
    {
      id: 's2',
      title: 'Matching',
      panes: [{ id: 'p', label: 'KcoreSpec/Evaluation.lean', source: patVal, lang: 'lean' }],
      frames: [
        { hl: { p: [lineOf(patVal, 'inductive PatVal')] }, notes: [note('p', lineOf(patVal, 'inductive PatVal'), 'A relation: the pattern `p` denotes the value `v` under the substitution σ.', 'inductive PatVal')], say: "A rule applies when its left-hand side ==denotes== the configuration under some substitution σ, a value for each variable." },
        { hl: { p: [lineOf(patVal, '| var {i : Nat}'), lineOf(patVal, '| ctor {f : Sym}')] }, notes: [note('p', lineOf(patVal, '| var {i : Nat}'), 'A variable denotes its value under σ.', 'σ.lookup i = some v'), note('p', lineOf(patVal, '| ctor {f : Sym}'), 'A constructor applied to patterns denotes the same constructor applied to their values.', '| ctor')] },
        { hl: { p: span(patVal, '| as {p : Term}', 'PatVal c σ (.as p i) v') }, notes: [note('p', lineOf(patVal, '| as {p : Term}'), 'An alias `p #as X` denotes what `p` denotes, and σ gives `X` that same value.', '| as')], say: `Rule 0's left-hand side denotes \`${k(c0)}\` under σ = \`${substText(m00.subst)}\`: \`N\` is \`z\`, and the alias \`s(N)\` is \`s(z)\`.` },
        { say: 'σ must also be ==well sorted==: each variable gets a value of its declared sort. Rule 1 needs `z` where this configuration has `s(z)`, so it has no σ at all.' },
      ],
    },
    {
      id: 's3',
      title: 'Evaluating the right-hand side',
      panes: [
        { id: 'e', label: 'KcoreSpec/Evaluation.lean', source: evalTerm, lang: 'lean' },
        { id: 'f', label: 'KcoreSpec/Evaluation.lean', source: evalEval, lang: 'lean' },
      ],
      frames: [
        { hl: { e: [lineOf(evalTerm, 'inductive EvalTerm')] }, notes: [note('e', lineOf(evalTerm, 'inductive EvalTerm'), 'The right-hand side `t` has the result `r` under σ: a value, or `none`, undefined.', 'inductive EvalTerm')], say: "Rule 0's right-hand side is `run(pred(X1))` around the same cells, where `X1` is the alias of `s(N)`." },
        { hl: { e: span(evalTerm, '/-- A constructor of `c` builds', 'EvalTerm c σ (.app f ts) ((allSome rs).map (.ctor f))') }, notes: [note('e', lineOf(evalTerm, '| ctor {σ : Subst}'), 'A constructor builds the tree from its arguments\' values.', '| ctor')] },
        { hl: { f: span(evalEval, '| clause {f : Sym}', '(hrhs : EvalTerm c σ cl.rhs r) : Eval c f vs r') }, notes: [note('f', lineOf(evalEval, '| clause {f : Sym}'), 'The first clause that applies decides.', '| clause')], say: `A call of a function is given by \`Eval\`. \`pred(s(z))\` matches the first clause \`pred(s(N)) = N\`, so its value is \`${predOf('s(z)')}\`.` },
        { hl: { f: span(evalEval, '| owise {f : Sym}', '(hrhs : EvalTerm c (argSubst 0 vs) o.rhs r) : Eval c f vs r') }, notes: [note('f', lineOf(evalEval, '| owise {f : Sym}'), 'Where every clause fails, the `[owise]` clause gives the result.', '| owise')], say: `\`pred(z)\` matches no clause, so the \`[owise]\` clause applies: its value is \`${predOf('z')}\`. Lesson 1 noted that peano's runs never call it.` },
        { hl: { f: span(evalEval, '| undef {f : Sym}', 'Eval c f vs none') }, notes: [note('f', lineOf(evalEval, '| undef {f : Sym}'), 'With no clause and no `[owise]`, the call is undefined.', '| undef')], say: `So under σ, rule 0's right-hand side evaluates to the configuration holding \`${kText(kItem(m00.rhs!))}\`.` },
      ],
    },
    {
      id: 's4',
      title: 'A step',
      panes: [{ id: 's', label: 'KcoreSpec/Step.lean', source: step, lang: 'lean' }],
      frames: [
        { hl: { s: span(step, 'inductive Step', '(hσ : c.WellSorted r.vars σ)') }, notes: [note('s', lineOf(step, '| rule {x y : Config c}'), 'One way to step: by a rule of the definition, under a well-sorted σ.', '(r : Rule) (mem : r ∈ c.rules) (σ : Subst)')], say: 'With those three pieces, a step is one constructor with a premise for each.' },
        { hl: { s: [lineOf(step, '(hmatch : PatVal'), lineOf(step, '(hreq :'), lineOf(step, '(heval :')] }, notes: [note('s', lineOf(step, '(hmatch : PatVal'), 'The left-hand side denotes x…', 'hmatch'), note('s', lineOf(step, '(hreq :'), '…the `requires`, if any, evaluates to `true`…', 'hreq'), note('s', lineOf(step, '(heval :'), '…and the right-hand side evaluates to y.', 'heval')] },
        { hl: { s: [lineOf(step, '(hprio :'), ...span(step, 'def NotApplies', 'RuleReqFails c σ r')] }, notes: [note('s', lineOf(step, '(hprio :'), 'And no rule of a smaller priority applies to x.', 'hprio')], say: "That last premise gives priorities their meaning. peano's two rules both have priority 50, so for peano it never excludes a step." },
        {
          hl: { s: [lineOf(step, '(heval :')] },
          say: `So \`${k(c0)}\` steps to \`${k(c1)}\` by rule 0, and \`${k(c1)}\` steps to \`${kText(kItem(m11.rhs!))}\` by rule 1, under σ = \`${substText(m11.subst)}\`.`,
          ask: {
            q: 'Can a step stop halfway, with `pred(s(z))` still unevaluated in the k cell?',
            options: ['Yes, evaluating `pred` is a step of its own', 'No: `heval` asks for the value of the whole right-hand side, functions included', 'Only when `pred` has no clause for its argument'],
            answer: 1,
            why: 'Functions are evaluated inside the step, as lesson 1 saw krust do. If the right-hand side were undefined, there would be no step.',
          },
        },
      ],
    },
    {
      id: 's5',
      title: 'Computing the steps',
      panes: [
        { id: 'x', label: 'KcoreSpec/Exec.lean', source: successors, lang: 'lean' },
        { id: 'u', label: 'Peano/Surface.lean', source: surface, lang: 'lean' },
      ],
      visual: (at) => (at >= 3 ? succRows(at - 3) : null),
      frames: [
        { hl: { x: span(successors, 'def successorsN', 'match (applying.map (·.1.prio)).min? with') }, notes: [note('x', lineOf(successors, 'def successorsN'), 'Every match of every rule, the rules of the smallest priority among those that apply, and their results.', 'successorsN')], say: '`Step` is a relation: it says which pairs are steps, but you cannot run it. The package also has a function that computes the next configurations.' },
        { hl: { x: [lineOf(successors, 'def successorsN')] }, notes: [note('x', lineOf(successors, 'def successorsN'), '`n` bounds how much evaluation it may do, since a function might not terminate.', '(n : Nat)')] },
        { hl: { u: span(surface, 'theorem step_iff', 'Exec.step_iff_of_ok c ok srReady matchReady x y') }, notes: [note('u', lineOf(surface, 'Step c x y ↔'), 'y is a step from x exactly when, for some fuel, the function lists y.', '↔')], say: 'The generated package proves the two agree for peano. So a fact the kernel computes with `successorsN` is a fact about `Step`.' },
        { say: "Here is lesson 1's run, recomputed by the function: `run(s(z))` has one successor…" },
        { say: '…`run(z)` has one…' },
        { say: '…and `done(z)` has none: the run stops.' },
        { say: '`done(s(z))`, which no run reaches, has none either…' },
        { say: '…and neither has the configuration with `#KConfigValue` in its k cell.' },
      ],
    },
    {
      id: 's6',
      title: 'What step_iff assumes',
      panes: [
        { id: 'i', label: 'KcoreSpec/StepIff.lean', source: stepIffOk, lang: 'lean' },
        { id: 'f', label: 'Peano/Facts.lean', source: facts, lang: 'lean' },
      ],
      frames: [
        { hl: { i: span(stepIffOk, 'theorem step_iff_of_ok', '(hmr : c.matchReady = true)') }, notes: [note('i', lineOf(stepIffOk, 'theorem step_iff_of_ok'), 'Proved once, for every definition that passes three checks.', 'step_iff_of_ok')], say: "`step_iff` is a theorem about ==every== definition. peano's version is one application." },
        { hl: { i: [lineOf(stepIffOk, 'hok'), lineOf(stepIffOk, 'hsr'), lineOf(stepIffOk, 'hmr')] }, notes: [note('i', lineOf(stepIffOk, 'hok'), "`ok`: the conditions of being well formed that the definition itself has to meet.", 'hok'), note('i', lineOf(stepIffOk, 'hsr'), 'Function names apart, and subsorts closed under composition.', 'hsr'), note('i', lineOf(stepIffOk, 'hmr'), 'Subsorts a strict order, and the map operations patterns may use are not constructors.', 'hmr')] },
        { hl: { f: span(facts, 'theorem srReady', 'theorem matchReady') }, notes: [note('f', lineOf(facts, 'theorem srReady'), 'Each check on peano is a decision the kernel ran, in the modules of `Peano/Facts/`; `ok` is in `Facts/Ok.lean`.', 'srReady_of_T')], say: "The decisions read the definition's ==tables==, such as each sort's supersorts. The generator computes them, and one more decision, `T_eq`, checks they are the definition's." },
      ],
    },
  ],
  quiz: [
    {
      q: 'Why does a statement over `Config c` cover `done(s(z))`, which no run reaches?',
      options: ['It does not', 'A `Config` is any well-sorted tree of the top cell\'s sort, reachable or not', 'Because `done(s(z))` is reachable from `run(s(z))`'],
      answer: 1,
      why: 'Reachability plays no part in what a configuration is.',
    },
    {
      q: 'What does `hprio` add to a step?',
      options: ['Nothing for any definition', 'A rule steps only if no rule of a smaller priority applies to the configuration', 'A rule of priority 50 always steps first'],
      answer: 1,
      why: "For peano both rules have one priority, so it excludes nothing; in IMP it orders `[owise]` rules last.",
    },
  ],
  checked: [
    "The matches, values and successors in these scenes were computed by compiled Lean on KCore's parse of peano's KORE, which the tie proves is the package's term.",
    "`Peano.step_iff`, by the kernel: the executable step lists exactly `Step`'s successors, from `ok`, `srReady` and `matchReady`, each a kernel decision.",
    'Read, not proved: that `Step` and the definitions it reads (`GroundTerm`, `sortOf`, `PatVal`, `EvalTerm`, `Eval`) say what a K step is. That is what `sound_and_complete`, stated with `sorry`, would prove.',
  ],
  tryit: [
    {
      say: 'In the kcore-spec package directory, with the library built, put this in a file and run `lake env lean FILE`. It prints `2`, the number of peano\'s rules:',
      cmd: "import KcoreSpec\nopen KCore\n#eval do\n  let k ← IO.ofExcept (Kore.parseDefinition (← IO.FS.readFile \"examples/peano/Peano/definition.kore\"))\n  let some d := Parse.parse k | throw (IO.userError \"no parse\")\n  IO.println (repr d.sem.rules.length)",
    },
  ],
}
