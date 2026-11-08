'use client'

// Lesson 10: the K tutorial's IMP in the IMP fragment (F2): what IMP needs beyond the builtin
// fragment, a run and two stuck programs computed by F2's executable step, priorities on a small
// probe, the step relation with its priority premise, which corpus definitions are in F2, and
// whether F2's step is deterministic. Every number and run comes from lean-lessons.json; the
// guards below fail the build when the computed facts stop being the ones the narration describes.

import type { ReactNode } from 'react'

import { type F2Binding, type F2Rule, fmt, lean, lineOf, type Source, source, span, textSource } from '../data'
import { type Lesson, note } from '../lesson'
import { Bar, Rows } from '../viz'

/** A text's lines from the first containing `needle` on, keeping the file's line numbers. */
function from(src: Source, needle: string): Source {
  const at = lineOf(src, needle)
  return { ...src, start: at, text: src.text.split('\n').slice(at - src.start).join('\n') }
}
// The panes start at the K text: imp.k at its copyright line, below the header that says where it
// was copied from; prio.k at its module, below a note for the package's own checks.
const impK = from(textSource('imp.k', lean.impK), '// Copyright')
const prioK = from(textSource('prio.k', lean.prioK), 'module PRIO')
const f2Step = source('f2Step')
const stepIff = source('f2StepIff')
const sortPredsSrc = source('f2SortPreds')
const detOK = source('f2DetOK')
const apart = source('f2Apart')
const deterministic = source('f2Deterministic')
const detExcept = source('f2DetExcept')
const kimpDetOK = source('kimpDetOK')
const kimpDeterministic = source('kimpDeterministic')
const kinkOverlaps = source('kinkOverlaps')
const kinkWitnesses = source('kinkWitnesses')
const kinkWitnessed = source('kinkWitnessed')
const witnesses = lean.factsF2.witnesses

const imp = lean.factsF2.imp
const run = (name: string) => {
  const found = lean.factsF2.runs.find((r) => r.program === name)
  if (!found) throw new Error(`lean lessons: no computed IMP run ${name}`)
  return found
}
const arith = run('arith')
const redeclare = run('redeclare')
const divzero = run('divzero')
const prioConfig = (name: string) => {
  const found = lean.factsF2.prio.configs.find((c) => c.name === name)
  if (!found) throw new Error(`lean lessons: no computed priority configuration ${name}`)
  return found
}
const goD = prioConfig('goD')
const goB = prioConfig('goB')
const det = lean.detF2
const kinkDiff = lean.diffF2.rows.find((r) => r.subject === 'kink-examples-imp-imp-imp')
const kimpCost = det.costs.find((c) => c.modules.includes('K_det'))
const kinkPairs = (det.kink.rules * (det.kink.rules - 1)) / 2
const mem = lean.membershipF2

// What the narration says about the computed facts; the build stops if they change.
const arithRules = [15, 15, 15, 16, 11, 11, 33, 2, 34, 10, 33, 1, 34, 10, 33, 3, 34, 10]
if (
  !imp.inF2 || imp.priorities.length !== 1 ||
  arith.steps.map((s) => s.rule).join() !== arithRules.join() || arith.steps.some((s) => s.choices !== 1) || !arith.stepsAreSuccessors ||
  redeclare.steps.length !== 1 || redeclare.blocked.length !== 1 || redeclare.blocked[0].rule.index !== 15 ||
  divzero.blocked.map((b) => b.rule.index).join() !== '1,17,19,34' ||
  goD.successors.length !== 1 || goD.successors[0].rule !== 0 || !goD.rules.every((r) => r.applies) ||
  goB.successors.length !== 1 || goB.successors[0].rule !== 1 || goB.rules[0].applies ||
  det.kink.overlaps.map((p) => p.join('-')).join() !== '17-19,21-23' || det.pass + det.fail !== det.texts || det.strict + det.branching !== det.fail ||
  witnesses.map((w) => w.pair.join('-')).join() !== '17-19,21-23' || !witnesses.every((w) => w.witnessOK && w.stepsAreSuccessors && w.successors.length === 2 && w.rules.every((r) => r.applies)) ||
  !kinkDiff || kinkDiff.differences + kinkDiff.errors !== 0 || !kimpCost ||
  lean.diffF2.differences + lean.diffF2.errors !== 0 ||
  mem.firstFailure['in F2'] !== mem.inF2 || mem.inF2 + mem.firstFailure.wf + mem.firstFailure.parse + mem.firstFailure.emit !== mem.texts
) {
  throw new Error('lean lessons: the computed IMP facts are not the ones lesson 10 describes')
}

// ---- small renderers ---------------------------------------------------------------------------

const sans = (text: ReactNode) => <span style={{ fontFamily: 'var(--f-sans)' }}>{text}</span>
/** Prose with `code` spans. */
const prose = (text: string) => sans(text.split('`').map((part, i) => (i % 2 ? <code key={i}>{part}</code> : part)))

/** Where a rule comes from in imp.k: its line, and for heating and cooling the `strict` it came from. */
const ruleText = (r: F2Rule) => (r.kind === 'rule' ? `line ${r.lines[0]}` : `${r.kind === 'heat' ? 'heating' : 'cooling'}, line ${r.lines[0]}`)
const rulesByIndex = new Map(arith.rules.map((r) => [r.index, r]))
const bindings = (m: F2Binding[]) => m.filter((b) => !b.var.startsWith('_')).map((b) => `${b.var} = ${b.value}`).join(', ')
const cell = (conf: string, name: string) => {
  const found = conf.match(new RegExp(`<${name}> (.*?) </${name}>`))?.[1]
  if (found === undefined) throw new Error(`lean lessons: ${conf} has no ${name} cell`)
  return found
}

/** arith, step by step: which rows light up at each frame. */
const traceLit: readonly (readonly [number, number] | null)[] = [null, [1, 4], [5, 6], [7, 9], [10, 10], [11, 18], null]
const trace = (at: number) => {
  const lit = traceLit[at]
  const rows = [
    { key: 's0', n: '', rule: 'start', k: arith.initial.k, state: arith.initial.state },
    ...arith.steps.map((s, i) => ({ key: `s${i + 1}`, n: String(i + 1), rule: ruleText(rulesByIndex.get(s.rule)!), k: s.cells.k, state: s.cells.state })),
  ]
  return (
    <Rows
      head={['', 'by', 'k cell', 'state cell']}
      rows={rows.map((r, i) => ({
        key: r.key,
        state: lit === null || lit === undefined ? undefined : i >= lit[0] && i <= lit[1] ? ('cur' as const) : ('faded' as const),
        cells: [r.n, sans(r.rule), r.k, r.state],
      }))}
    />
  )
}

const sortPredTable = () => (
  <Rows
    head={['the item', 'its sort', 'isKResult, computed']}
    rows={lean.factsF2.sortPreds.map((p) => ({ key: p.item, cells: [p.item, p.sort, p.isKResult] }))}
  />
)

/** The rules that match a stuck configuration, each with its match and its `requires`. */
const blockedTable = (r: typeof divzero, lit?: readonly number[]) => (
  <Rows
    head={['rule that matches', 'its match', 'requires, which is not true']}
    rows={r.blocked.map((b) => ({
      key: String(b.rule.index),
      state: lit === undefined ? undefined : lit.includes(b.rule.index) ? ('cur' as const) : ('faded' as const),
      cells: [sans(ruleText(b.rule)), b.matches.map(bindings).join(' | '), b.rule.requires ?? ''],
    }))}
  />
)
const stuckView = (at: number) => {
  const r = at === 0 ? redeclare : divzero
  return (
    <>
      <div style={{ flex: 'none' }}>
        <Rows
          head={[`${r.program}, where it stops`, '']}
          rows={[
            { key: 'k', cells: [sans('k cell'), cell(r.final, 'k')] },
            { key: 'state', cells: [sans('state cell'), cell(r.final, 'state')] },
          ]}
        />
      </div>
      {blockedTable(r, at === 2 ? [17, 19, 34] : at === 1 ? [1] : undefined)}
    </>
  )
}

const prioTable = (at: number) => (
  <Rows
    head={['', 'rule', 'priority', 'applies', 'successor, computed']}
    rows={[goD, goB].flatMap((c, ci) =>
      c.rules.map((r, i) => ({
        key: `${c.name}${i}`,
        state: at < 2 ? undefined : at - 2 === ci ? ('cur' as const) : ('faded' as const),
        cells: [
          i === 0 ? c.k : '',
          sans(`line ${r.rule.lines[0]}`),
          r.rule.priority,
          sans(r.applies ? 'yes' : 'no'),
          c.successors.find((s) => s.rule === r.rule.index)?.k ?? '',
        ],
      })),
    )}
  />
)

const differential = (at: number) => (
  <Rows
    head={['F₂ execution differential', { text: '', num: true }]}
    rows={[
      { key: 'defs', cells: ['definitions', lean.diffF2.subjects] },
      { key: 'configs', cells: ['configurations compared with krust', fmt(lean.diffF2.compared)] },
      { key: 'diff', state: at === 1 ? ('cur' as const) : undefined, cells: ['differences and errors', lean.diffF2.differences + lean.diffF2.errors] },
      { key: 'branch', cells: ['with several successors', fmt(lean.diffF2.branching)] },
      { key: 'stuck', cells: ['stuck', fmt(lean.diffF2.stuck)] },
      { key: 'cap', cells: ['left unexplored at the size cap', fmt(lean.diffF2.unexplored)] },
    ].map((r) => ({ ...r, cells: [sans(r.cells[0]), r.cells[1]] }))}
  />
)

const membership = (at: number) => {
  const rows = [
    { key: 'in', what: 'in F₂', n: mem.inF2, variant: undefined },
    { key: 'parse', what: 'not read: the KORE uses something F₂ lacks', n: mem.firstFailure.parse, variant: 'alt' as const },
    { key: 'wf', what: 'read, but rejected by the well-formedness check', n: mem.firstFailure.wf, variant: 'alt' as const },
    { key: 'emit', what: 'read and well formed, but printed back differently', n: mem.firstFailure.emit, variant: 'alt' as const },
  ]
  return (
    <Rows
      head={[`the corpus's ${mem.texts} KORE texts`, { text: '', num: true }, { text: '', bar: true }]}
      rows={rows.map((r, i) => ({
        key: r.key,
        state: at === 0 ? (i === 0 ? ('cur' as const) : undefined) : i === 0 ? ('faded' as const) : ('cur' as const),
        cells: [sans(r.what), r.n, <Bar key="b" pct={(r.n / mem.texts) * 100} variant={r.variant} />],
      }))}
    />
  )
}

const witnessTable = (at: number) => (
  <Rows
    head={['configuration (k cell)', 'rule', 'successor (k cell), computed']}
    rows={witnesses.flatMap((w) =>
      w.successors.map((s, i) => ({
        key: `${w.name}${s.rule}`,
        state: at === 2 ? ('cur' as const) : undefined,
        cells: [i === 0 ? w.cells.k : '', sans(`${ruleText(w.rules.find((r) => r.rule.index === s.rule)!.rule)} (${s.rule})`), s.k],
      })),
    )}
  />
)

const corpus = (at: number) => {
  const names = (kind: 'strict' | 'branching') => det.failing.filter((f) => f.kind === kind).map((f) => f.name).join('; ')
  return (
    <Rows
      head={[`the ${det.texts} texts in F₂`, { text: '', num: true }, '']}
      rows={[
        { key: 'pass', state: at === 0 ? ('cur' as const) : undefined, cells: [prose('`detOK` holds: deterministic'), det.pass, ''] },
        { key: 'strict', state: at === 1 ? ('cur' as const) : undefined, cells: [prose('two heating rules of one `strict` operator'), det.strict, sans(names('strict'))] },
        { key: 'branching', state: at === 2 ? ('cur' as const) : undefined, cells: [sans('branching on purpose: tests of several successors'), det.branching, sans(names('branching'))] },
      ]}
    />
  )
}

// ---- the lesson --------------------------------------------------------------------------------

export const lesson10: Lesson = {
  id: 'imp-fragment',
  number: 10,
  title: 'The IMP fragment',
  scenes: [
    {
      id: 'imp',
      title: 'A small imperative language',
      panes: [{ id: 'k', label: 'imp.k', source: impK, lang: 'k' }],
      frames: [
        { say: "IMP is the K tutorial's small imperative language: integer and boolean expressions, assignment, blocks, `if`, `while`, and declarations of variables. Its definition doesn't fit the builtin fragment. The ==IMP fragment==, F₂, is the builtin fragment plus what IMP's KORE needs, and Lean checks that IMP is in it." },
        {
          hl: { k: [lineOf(impK, 'syntax AExp'), lineOf(impK, 'syntax KResult')] },
          notes: [
            note('k', lineOf(impK, 'syntax AExp'), "an integer is an arithmetic expression", 'Int'),
            note('k', lineOf(impK, 'syntax KResult'), "and a result: evaluation stops at it", 'KResult'),
          ],
          say: "`Int` is below " + imp.supersortsOfInt.length + " sorts: " + imp.supersortsOfInt.join(', ') + " (the last from K's library). The builtin fragment allows a sort one supersort, so ==several supersorts== are the first thing F₂ adds.",
        },
        {
          hl: { k: [lineOf(impK, 'AExp "/" AExp'), lineOf(impK, 'AExp "+" AExp'), lineOf(impK, 'Id "=" AExp ";"')] },
          notes: [note('k', lineOf(impK, 'Id "=" AExp ";"'), "evaluate the second argument first", 'strict(2)')],
          say: "`strict` says to evaluate an argument before the operator's own rule applies. kompile turns each strict argument into two rules, so IMP's " + imp.rules + " rules are " + imp.ruleKinds.rule + " written here and " + imp.ruleKinds.heat + " pairs from `strict`. The run below shows what the pairs do.",
        },
        {
          hl: { k: span(impK, 'rule <k> int (X,Xs => Xs)', 'requires notBool (X in keys(Rho))') },
          notes: [note('k', lineOf(impK, 'requires notBool (X in keys(Rho))'), "the keys of the state map: a set", 'keys(Rho)')],
          say: "Declaring a variable checks that it isn't declared yet, by membership in a ==set==, the state's keys. F₂ adds set values and these two operations.",
        },
        {
          hl: { k: [lineOf(impK, 'imports DOMAINS', lineOf(impK, 'imports DOMAINS-SYNTAX'))] },
          notes: [note('k', lineOf(impK, 'imports DOMAINS', lineOf(impK, 'imports DOMAINS-SYNTAX')), "Int, Bool, maps, sets, names and more", 'DOMAINS')],
          say: "IMP imports K's whole `DOMAINS` library, where the builtin fragment knew only Bool, Int and maps.",
        },
        {
          hl: { k: [lineOf(impK, 'syntax Id ::= "n"'), lineOf(impK, '| "sum"')] },
          notes: [note('k', lineOf(impK, 'syntax Id ::= "n"'), "`Id` is a token sort: its values are names", 'token')],
          say: "Its variables are ==tokens== of the sort `Id`. F₂ has those too.",
        },
      ],
    },
    {
      id: 'run',
      title: 'A run, computed',
      arrange: 'wide',
      visual: trace,
      panes: [{ id: 'k', label: 'imp.k', source: impK, lang: 'k' }],
      frames: [
        { say: "This program declares three variables and assigns them. Lean's executable step for F₂ ran it to the end: " + arith.length + " steps, and at each step exactly one successor." },
        {
          hl: { k: span(impK, 'rule <k> int (X,Xs => Xs)', 'rule int .Ids; S => S') },
          notes: [note('k', lineOf(impK, 'rule <k> int (X,Xs => Xs)'), "one name per step, mapped to 0", 'X|->0')],
        },
        {
          hl: { k: [lineOf(impK, 'rule S1:Stmt S2:Stmt')] },
          notes: [note('k', lineOf(impK, 'rule S1:Stmt S2:Stmt'), "two statements become one after the other", '~>')],
        },
        {
          hl: { k: [lineOf(impK, 'Id "=" AExp ";"'), lineOf(impK, 'rule I1 + I2')] },
          notes: [note('k', lineOf(impK, 'Id "=" AExp ";"'), "this `strict(2)` made the heating and the cooling rule", 'strict(2)')],
          say: "==Heating== takes `2 + 3` out of the assignment and leaves `a = □;`, a constructor kompile declares for the hole, called a ==freezer==. `+` turns `2 + 3` into 5. ==Cooling== puts 5 back in the hole.",
        },
        {
          hl: { k: [lineOf(impK, 'rule <k> X = I:Int;')] },
          notes: [note('k', lineOf(impK, 'rule <k> X = I:Int;'), "the entry for `X` gets the new value", '_ => I')],
        },
        {
          hl: { k: [lineOf(impK, 'rule I1 / I2'), lineOf(impK, 'rule - I1')] },
          say: "`b` and `c` go the same way, through `/` and unary minus. The run ends with an empty k cell and the state " + cell(arith.final, 'state') + ".",
        },
        {
          say: "In `7 / 2`, `/` is strict in both operands, yet neither was heated.",
          ask: {
            q: "Why was neither operand of `7 / 2` heated?",
            options: ["Heating only applies inside assignments", "Both are already results: a heating rule requires that what it takes out is not a `KResult`", "The `/` rule has a higher priority than heating"],
            answer: 1,
            why: "Each heating rule has `requires notBool isKResult(HOLE)`. 7 and 2 are integers, and integers are results.",
          },
        },
      ],
    },
    {
      id: 'results',
      title: 'When heating stops',
      visual: sortPredTable,
      panes: [{ id: 's', label: 'Sort predicates (frozen)', source: sortPredsSrc }],
      frames: [
        {
          hl: { s: span(sortPredsSrc, '/-- The generated sort predicates', 'These are the equations kompile writes') },
          say: "`isKResult` is a ==sort predicate==: a function that says whether an item is of a sort. kompile writes one for every sort, as equations; F₂ reads them as functions. IMP has " + imp.sortPreds + ".",
        },
        {
          hl: { s: span(sortPredsSrc, 'c.sortsBelowKItem.map fun X =>', 'some ⟨["K"], ff⟩⟩') },
          notes: [note('s', lineOf(sortPredsSrc, '⟨"Lblis" ++ X'), "true on an item of sort X, false on any other", 'Lblis')],
          say: "Lean computed the table. An integer or a boolean is a result. A name or an expression is not, so heating takes it out.",
        },
      ],
    },
    {
      id: 'stuck',
      title: 'Where a run stops',
      visual: stuckView,
      panes: [{ id: 'k', label: 'imp.k', source: impK, lang: 'k' }],
      frames: [
        {
          hl: { k: span(impK, 'rule <k> int (X,Xs => Xs)', 'requires notBool (X in keys(Rho))') },
          notes: [note('k', lineOf(impK, 'requires notBool (X in keys(Rho))'), "`a` is already a key", 'X in keys(Rho)')],
          say: "`int a, a;` declares `a` twice. After the first declaration the declaration rule still matches, but its `requires` is false, and no other rule matches. The configuration is ==stuck==: it has no successor.",
        },
        {
          hl: { k: [lineOf(impK, 'rule I1 / I2')] },
          notes: [note('k', lineOf(impK, 'rule I1 / I2'), "the divisor is 0", 'I2 =/=Int 0')],
          say: "`a = 1 / 0;` heats `1 / 0` out of the assignment and stops there. Four rules match it. The division rule's `requires` is false.",
        },
        {
          hl: { k: [lineOf(impK, 'AExp "/" AExp'), lineOf(impK, 'Id "=" AExp ";"')] },
          say: "The two heating rules of `/` match too, but 1 and 0 are already results. And cooling would put `1 / 0` back into the assignment, but it isn't a result. Each `requires` is false, so the run is stuck, which is what the definition says division by zero is.",
          ask: {
            q: "Is a stuck configuration an error in the step?",
            options: ["Yes: Lean's step should always find a rule", "No: it is the definition's own answer. No rule applies, so there is no step, and krust and K's backend stop at the same configuration", "Only when the program is wrong"],
            answer: 1,
            why: "The definition gives division by zero no rule. A stuck configuration is how K says a program went wrong.",
          },
        },
      ],
    },
    {
      id: 'prio',
      title: 'Priorities',
      visual: prioTable,
      arrange: 'top',
      panes: [{ id: 'p', label: 'prio.k', source: prioK, lang: 'k' }],
      frames: [
        {
          hl: { p: span(prioK, 'rule <k> go(X:D)', 'rule <k> go(_)') },
          notes: [
            note('p', lineOf(prioK, 'rule <k> go(X:D)'), "tried first", 'priority(40)'),
            note('p', lineOf(prioK, 'rule <k> go(_)'), "only if no other rule applies", 'owise'),
          ],
          say: "IMP's rules all have the same priority, so this small definition shows the other thing F₂ adds. A rule with a smaller priority is tried first. The default is 50, and `[owise]` means 200: last.",
        },
        {
          hl: { p: span(prioK, 'syntax D ::=', 'syntax C ::=') },
          notes: [note('p', lineOf(prioK, 'syntax C ::='), "D is below both B and C", 'D')],
        },
        { say: "On `" + goD.k + "` all three rules apply. Only the one with the smallest priority steps: `" + goD.successors[0].k + "`." },
        {
          say: "On `" + goB.k + "` the first rule doesn't match, since `b` isn't a D. Of the two that apply, priority 50 comes before 200: `" + goB.successors[0].k + "`.",
          ask: {
            q: "Without `[priority(40)]`, what would `go(d)` step to?",
            options: ["`out(d)` only", "Both `out(d)` and `other(d)`: the first two rules would both have priority 50, and both apply", "`stop()`"],
            answer: 1,
            why: "Rules of one priority that both apply each give a successor. That's the question of the end of this lesson.",
          },
        },
      ],
    },
    {
      id: 'step',
      title: 'One more premise',
      panes: [{ id: 's', label: 'The step of F₂ (frozen)', source: f2Step }],
      frames: [
        {
          hl: { s: span(f2Step, 'inductive Step (c : Semantics)', '(hprio :') },
          notes: [note('s', lineOf(f2Step, '(hprio :'), "no rule of a smaller priority applies here", 'hprio')],
          say: "F₂'s step is the builtin fragment's with one more premise: a rule steps only when no rule of a smaller priority applies.",
        },
        {
          hl: { s: span(f2Step, '/-- `NotApplies c r x`', 'PatVal c σ r.lhs x → RuleReqFails c σ r') },
          say: "\"Doesn't apply\" is again a denotation: under every well-sorted match, the `requires` is not `true`. In lesson 6's terms, the relation and what it reads are " + fmt(lean.f2Cones.step.totals.total.coneLines) + " lines.",
        },
      ],
    },
    {
      id: 'iff',
      title: 'Proved equal, and compared',
      visual: differential,
      arrange: 'top',
      panes: [{ id: 'i', label: 'step_iff for F₂ (checked)', source: stepIff }],
      frames: [
        {
          hl: { i: span(stepIff, '/-- The executable step lists exactly', 'step_iff_of d hwf') },
          say: "As for the builtin fragment, `step_iff` proves that the executable step lists exactly the relation's successors, for every well-formed definition. So the run, the stuck configurations and the priority table are facts about `Step`.",
        },
        {
          say: "Compared with krust on " + lean.diffF2.subjects + " definitions in F₂, " + fmt(lean.diffF2.compared) + " configurations had the same successors, with " + (lean.diffF2.differences + lean.diffF2.errors) + " differences. " + fmt(lean.diffF2.branching) + " of them had several successors.",
        },
      ],
    },
    {
      id: 'members',
      title: 'Which definitions are in it',
      visual: membership,
      frames: [
        { say: "Lesson 3's round trip decides membership: read the KORE into an F₂ definition, check it's well formed, and print it back. Of the corpus's " + mem.texts + " KORE texts, " + mem.inF2 + " pass." },
        { say: "For the others, the table gives the first stage that fails. Some of what F₂ leaves out on purpose: `ensures`, lists, set and list patterns in left-hand sides, String operations, and symbols whose sorts are parameters, such as `#if`." },
      ],
    },
    {
      id: 'branch',
      title: 'Can a step branch?',
      panes: [{ id: 'd', label: 'Determinism (checked)', source: deterministic }],
      frames: [
        { say: "`Step` is a relation, so a configuration can have several successors. A program in IMP should have at most one. That's ==determinism==, and it depends on the definition." },
        {
          hl: { d: span(deterministic, 'theorem deterministic_of', '(hd : detOK c = true)') },
          notes: [
            note('d', lineOf(deterministic, '(hd : detOK c = true)'), "two steps from x reach one configuration", "y = y'"),
            note('d', lineOf(deterministic, 'theorem deterministic_of'), "the three facts `step_iff` already uses", 'hok'),
          ],
          say: "One theorem covers every F₂ definition: where a condition `detOK` holds, two steps from one configuration reach one configuration. `detOK` is a program returning a Bool, so for a given definition the kernel can decide it by computing.",
        },
      ],
    },
    {
      id: 'condition',
      title: 'The condition',
      panes: [
        { id: 'o', label: 'detOK (reviewed layer)', source: detOK },
        { id: 'a', label: 'Two rules apart', source: apart },
      ],
      frames: [
        {
          hl: { o: span(detOK, '/-- The condition:', 'c.rules.all (uniqOK c)') },
          notes: [note('o', lineOf(detOK, 'c.rules.all (uniqOK c)'), "one rule alone gives one result", 'uniqOK')],
          say: "First, each rule alone: its match must fix everything its right-hand side uses.",
        },
        {
          hl: { o: [lineOf(detOK, "r.prio != r'.prio")] },
          notes: [note('o', lineOf(detOK, "r.prio != r'.prio"), "different priorities: `hprio` already keeps the later one out", "r.prio != r'.prio")],
          say: "Then every two rules. Two rules of different priorities never both step from one configuration.",
        },
        {
          hl: { o: [lineOf(detOK, "r.prio != r'.prio")], a: span(apart, '/-- Rules r and r\' never both apply', 'clashes c r\'.vars') },
          notes: [note('a', lineOf(apart, '| none => true'), "the left-hand sides can't match one configuration", 'none')],
          say: "Two rules of one priority must be ==apart==: no configuration lets both apply. Either their left-hand sides can't match one configuration, or, where both match, their conditions clash.",
        },
        {
          hl: { a: span(apart, '/-- No σ\' (well-sorted for `vs`)', "b != b' && Term.beq A A'") },
          notes: [note('a', lineOf(apart, "b != b' && Term.beq A A'"), "one condition true in one rule and false in the other", "b != b'")],
          say: "They clash when the sorts refute one, when one without variables evaluates to false, or when one rule needs a condition true and the other needs it false. IMP's `<=` is `seqstrict`: its right operand is heated only once the left is a result, and its left only while it isn't. Those conditions clash, so the two heating rules are apart.",
        },
      ],
    },
    {
      id: 'kimp',
      title: 'A deterministic IMP',
      panes: [
        { id: 'c', label: 'The check (kernel)', source: kimpDetOK },
        { id: 't', label: 'The theorem', source: kimpDeterministic },
      ],
      frames: [
        {
          hl: { c: [lineOf(kimpDetOK, 'theorem kimp_detOK')] },
          notes: [note('c', lineOf(kimpDetOK, 'theorem kimp_detOK'), "the kernel runs `detOK`", 'decide +kernel')],
          say: "kimp is a larger IMP, from Runtime Verification's imp-semantics: " + det.kimp.rules + " rules, so " + fmt(det.kimp.pairs) + " pairs. The kernel decides `detOK` for it in " + kimpCost?.seconds + " seconds, at " + kimpCost?.peak + ".",
        },
        {
          hl: { t: span(kimpDeterministic, 'theorem kimp_deterministic', '#print axioms kimp_deterministic') },
          notes: [note('t', lineOf(kimpDeterministic, 'Det.deterministic_of'), "the general theorem, applied", 'deterministic_of')],
          say: "So kimp's step is deterministic, with Lean's three axioms only.",
        },
      ],
    },
    {
      id: 'overlaps',
      title: 'This IMP: two overlaps',
      panes: [
        { id: 'k', label: 'imp.k', source: impK, lang: 'k' },
        { id: 'o', label: 'The overlaps (kernel)', source: kinkOverlaps },
      ],
      frames: [
        {
          hl: { k: [lineOf(impK, 'AExp "/" AExp'), lineOf(impK, 'AExp "+" AExp')] },
          notes: [note('k', lineOf(impK, 'AExp "/" AExp'), "either operand may be heated first", 'strict')],
          say: "This lesson's IMP fails `detOK`, on exactly 2 of its " + kinkPairs + " pairs. `/` and `+` are `strict`, not `seqstrict`: when neither operand is a result, either can be heated first.",
        },
        {
          hl: { o: span(kinkOverlaps, '/-- kink IMP', 'theorem kink_detOKExcept') },
          notes: [note('o', lineOf(kinkOverlaps, 'def kinkOverlaps'), "the heating rules of `/` (17, 19) and of `+` (21, 23)", '(17, 19)')],
          say: "`detOKExcept` is the same condition with a list of pairs let through. With these two pairs, the kernel decides it for this IMP.",
        },
        {
          hl: { k: [lineOf(impK, 'AExp "<=" AExp'), lineOf(impK, 'BExp "&&" BExp')] },
          say: "`<=` is `seqstrict`, and `&&` is strict in its first argument only, so neither appears in the list.",
        },
      ],
    },
    {
      id: 'except',
      title: 'Deterministic, except there',
      panes: [{ id: 'e', label: 'Up to listed overlaps (checked)', source: detExcept }],
      frames: [
        {
          hl: { e: span(detExcept, 'theorem deterministic_except', "Applies c c.rules[i] x.val ∧ Applies c c.rules[j] x.val") },
          notes: [note('e', lineOf(detExcept, "y = y' ∨"), "one result, or both rules of a listed pair apply", '∨')],
          say: "With pairs let through, the general theorem says less: two steps reach one configuration, ==or== both rules of a listed pair apply there. For this IMP that pins any branching on `/` or `+`.",
        },
      ],
    },
    {
      id: 'witnessed',
      title: 'Both overlaps are real',
      visual: witnessTable,
      arrange: 'top',
      panes: [
        { id: 'w', label: 'The witnesses (kernel)', source: kinkWitnesses },
        { id: 'r', label: 'Every overlap branches (kernel)', source: kinkWitnessed },
      ],
      frames: [
        {
          hl: { w: span(kinkWitnesses, 'theorem kinkDiv_witness', 'theorem kinkAdd_witness') },
          notes: [note('w', lineOf(kinkWitnesses, 'theorem kinkDiv_witness'), "at `" + witnesses[0].cells.k + "`: both rules apply, and two different successors", 'kinkDiv')],
          say: "Is each listed pair a real branching, or could the condition just be too strict? For each pair the kernel checks one configuration, `" + witnesses[0].cells.k + "` and `" + witnesses[1].cells.k + "`, where both rules apply and the step has two different successors.",
        },
        {
          hl: { r: span(kinkWitnessed, 'theorem kink_overlaps_witnessed', "y ≠ y'") },
          say: "So the list is exact both ways: every branching of this IMP comes from a listed pair, and every listed pair branches.",
        },
        {
          say: "The table gives each rule's successor, as Lean computed it. The kernel's facts are only that both rules apply and that the successors differ. The differential agrees: " + kinkDiff?.branching + " configurations of this IMP had several successors, and krust listed the same ones.",
          ask: {
            q: "What would make this IMP deterministic?",
            options: ["Giving the heating rules priorities", "Declaring `/` and `+` `seqstrict`: the heating conditions would then clash", "Removing the cooling rules"],
            answer: 1,
            why: "That is how `<=` is declared, and its pair is apart. Priorities would also separate the pairs, but they would change which programs can be evaluated in which order, not just make a choice explicit.",
          },
        },
      ],
    },
    {
      id: 'corpus',
      title: 'Across the corpus',
      visual: corpus,
      frames: [
        { say: "Of the " + det.texts + " texts in F₂, " + det.pass + " pass `detOK`, so their steps are deterministic." },
        { say: det.strict + " fail on two heating rules of one `strict` operator, as this IMP does." },
        { say: "The other " + det.branching + " are tests written to have several successors. Every failure is a real overlap." },
      ],
    },
  ],
  quiz: [
    {
      q: "Why does IMP's `<=` have no overlap while `+` has one?",
      options: ["`<=` returns a Bool", "`<=` is `seqstrict`: its right operand is heated only once the left is a result, and its left only while it isn't, so the two heating rules' conditions clash", "`<=` has fewer rules"],
      answer: 1,
      why: "`+` is `strict`, so both heating rules can apply to `x + y`.",
    },
    {
      q: "In `divzero`, four rules match the final configuration. Why is it stuck?",
      options: ["The step ran out of fuel", "The `requires` of each is false: the divisor is 0, 1 and 0 are results, and `1 / 0` isn't", "Division by zero crashes the evaluator"],
      answer: 1,
      why: "A rule steps only when it matches and its `requires` is `true`.",
    },
    {
      q: "Why do two rules of different priorities need no check in `detOK`?",
      options: ["Priorities are rare", "`Step`'s priority premise lets a rule step only when no rule of a smaller priority applies, so they never both step from one configuration", "The kernel can't compare priorities"],
      answer: 1,
      why: "That's the premise `hprio`.",
    },
  ],
  checked: [
    "Checked by the Lean kernel, with the axioms `propext`, `Classical.choice` and `Quot.sound` only, for every definition F₂'s `wf` accepts: `step_iff`; `deterministic_of`, `deterministic_except` and `witnessed_of`. The build pins their axiom lists.",
    "By the kernel, for the priority probe and peano: that their KORE is in F₂ (`prio_F2`, `peano_F2`) and their `step_iff`.",
    "By the kernel, for this IMP's core (the Lean value read from its KORE): the three facts `step_iff` uses and so `kink_step_iff`, `detOKExcept` with its two pairs, the two witnesses and `kink_overlaps_witnessed`. That this core is what Lean reads from IMP's KORE is a compiled check, not a kernel one; `test/f2-det.sh` runs it last.",
    "By the kernel, outside the package, since kimp's KORE isn't in it: `detOK` for kimp (" + fmt(det.kimp.pairs) + " pairs) and `kimp_deterministic`.",
    "Computed, not proved: that IMP is in F₂; the run of `arith`, the two stuck programs, the priority table, the sort predicates and which rule gives which witness successor, by Lean's compiled evaluation of the executable step, which `step_iff` proves equal to `Step`. The corpus counts, for membership and for `detOK`, were computed the same way, by scripts outside the build.",
    "Evidence, not proof: the F₂ execution differential, " + fmt(lean.diffF2.compared) + " configurations of " + lean.diffF2.subjects + " definitions, " + (lean.diffF2.differences + lean.diffF2.errors) + " differences against krust. " + fmt(lean.diffF2.unexplored) + " configurations were left unexplored at the size cap.",
    "Not proved: that F₂'s step is sound and complete, [lesson 8](/lean/sound-and-complete).",
  ],
  tryit: [
    {
      say: "In the kcore-spec package directory, in this order:",
      cmd: "lake build          # F2's definitions and the general theorems, with their axiom checks\ntest/f2-kernel.sh   # peano and the priority probe in F2, and step_iff for both, by the kernel\ntest/f2-det.sh      # this IMP: its core's facts, the overlaps and the witnesses, by the kernel; about a minute",
    },
    {
      say: "Each script checks one module per process and prints a line for each, `NAME: exit 0, N s, peak RSS M MB`. `test/f2-det.sh` ends with the compiled check that ties the core to IMP's KORE:",
      cmd: "Tie: parse f2-examples/imp.kore gives kinkSem: true (37 rules)",
    },
  ],
}
