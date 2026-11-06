'use client'

// Lesson "What a step means in Lean": peano's run(s(z)) → run(z) → done(z), on the real
// definitions. Terms, substitutions, values and successors are the ones Lean computed on
// peanoCore (the generator's Facts.lean); source panes are the files at the recorded commit.

import type { ReactNode } from 'react'

import {
  type Explain,
  config,
  groundText,
  kItem,
  koreAxiom,
  lean,
  lineOf,
  patternText,
  peanoK,
  ruleFact,
  source,
  span,
  substText,
} from './data'
import { type Pane, LessonScene, type Step } from './LessonScene'
import styles from './Lesson.module.css'
import { GroundView, PatternView, SubstView, TermBox } from './Terms'

const value = source('Value')
const evaluation = source('Evaluation')
const step = source('Step')
const core = source('PeanoCore')
const kore1 = koreAxiom('rule', 0)

const c0 = config('c0')
const c1 = config('c1')
const c2 = config('c2')
const succ0 = ruleFact(c0, 'runSucc')
const zero0 = ruleFact(c0, 'runZero')
const zero1 = ruleFact(c1, 'runZero')
const rules = Object.fromEntries(lean.facts.rules.map((r) => [r.name, r]))
const predOf = (arg: string) => {
  const found = lean.facts.pred.find((p) => groundText(p.arg) === arg)
  if (!found) throw new Error(`lean lessons: no computed pred(${arg})`)
  return found
}

// What the scenes say must be what Lean computed.
const expect = (what: string, actual: string, wanted: string) => {
  if (actual !== wanted) throw new Error(`lean lessons: ${what} is ${actual}, the scene says ${wanted}`)
}
expect('the sort of c0', String(c0.sort), 'GeneratedTopCell')
expect('runSucc on c0', substText(succ0.match ?? []), '[X0 ↦ z, X1 ↦ s(z), X2 ↦ <generatedCounter>(\\dv{Int}("0"))]')
expect('runZero on c0', String(zero0.match), 'null')
expect('successors of c0', (c0.successors ?? []).map(groundText).join(' | '), groundText(c1.term))
expect('successors of c1', (c1.successors ?? []).map(groundText).join(' | '), groundText(c2.term))
expect('successors of c2', String(c2.successors?.length), '0')
expect('pred(s(z))', groundText(predOf('s(z)').value!), 'z')
expect('pred(z)', `${groundText(predOf('z').value!)} by ${predOf('z').explain.call?.by}`, 'z by owise')
expect('pred of an Int', `${groundText(predOf('\\dv{Int}("5")').value!)} by ${predOf('\\dv{Int}("5")').explain.call?.by}`, 'z by owise')
expect('evalReady peanoCore', String(lean.facts.evalReady), 'true')

const kc = (t: Parameters<typeof kItem>[0]) => groundText(kItem(t))

// ---- 1. A configuration is a tree --------------------------------------------------------

export function ConfigurationScene() {
  const panes: Pane[] = [{ id: 'v', label: 'Ground terms and their sorts', source: value }]
  const marks: (readonly number[] | undefined)[] = [undefined, undefined, [0, 0, 0, 0], [0, 0, 0], [1, 0], undefined, undefined, undefined]
  const steps: Step[] = [
    { say: <>The configuration we will run: <code>run(s(z))</code> in the k cell, and the counter cell that krust's initial configuration has.</> },
    { say: <>In Lean it is a <code>GroundTerm</code>: a plain tree with three kinds of node.</>, hl: { v: span(value, 'inductive GroundTerm where', 'deriving Repr, Inhabited') } },
    { say: <><code>ctor</code> is a constructor applied to arguments, named by its KORE symbol: the data writes <code>s</code> as <code>Lbls</code> and <code>&lt;k&gt;</code> as <code>Lbl'-LT-'k'-GT-'</code>.</>, hl: { v: [lineOf(value, '| ctor (f : String)')] } },
    { say: <><code>inj</code> is an injection along a subsort: <code>inj{'{'}State,KItem{'}'}</code> puts the <code>State</code> <code>run(s(z))</code> where the K sequence expects a <code>KItem</code>.</>, hl: { v: [lineOf(value, '| inj (a b : String) (t : GroundTerm)')] } },
    { say: <><code>dv</code> is a domain value of a builtin sort: the counter's 0 is <code>\dv{'{'}Int{'}'}("0")</code>.</>, hl: { v: [lineOf(value, '| dv (s : String) (lit : String)')] } },
    { say: <>The type says nothing about sorts. <code>sortOf</code> computes a tree's sort from the definition's data, or <code>none</code>.</>, hl: { v: span(value, 'def sortOf : GroundTerm → Option String', 'termination_by structural t => t') } },
    { say: <>A constructor must be declared and get exactly its argument sorts; an injection must follow a declared subsort and must not sit directly on another injection.</>, hl: { v: [lineOf(value, '| some k => if sortsOf ts == some k.args'), lineOf(value, '| .inj a b t => if c.subsorts.contains (a, b)')] } },
    { say: <>Lean computes <code>sortOf</code> of this tree as <code>{c0.sort}</code>, so it is a <code>Config</code>: a value of the configuration sort.</>, hl: { v: [...span(value, 'def Value (c : Semantics)', 'def Value (c : Semantics)'), lineOf(value, 'abbrev Config (c : Semantics)')] } },
  ]
  return (
    <LessonScene
      title="A configuration is a tree"
      panes={panes}
      steps={steps}
      visual={(at) => (
        <TermBox label={at === steps.length - 1 ? `c0, of sort ${c0.sort}` : 'c0'}>
          <GroundView term={c0.term} mark={marks[at]} />
        </TermBox>
      )}
      questions={[
        { q: <>Why does <code>inj{'{'}Val,KItem{'}'}(inj{'{'}Nat,Val{'}'}(z))</code> have no sort, while <code>inj{'{'}Nat,KItem{'}'}(z)</code> has one?</>,
          a: <>The two denote the same element in every model of the definition's theory, so only one may represent it. <code>sortOf</code> rejects an injection directly on another, and every sort below <code>KItem</code> has its own pair <code>(X, KItem)</code> in the subsort list, so the second form exists for every such sort.</> },
        { q: <>Is <code>\dv{'{'}Int{'}'}("abc")</code> a value of sort <code>Int</code>?</>,
          a: <>Yes: any literal string is accepted as a domain value of a base sort. The configurations are therefore a superset of K's, and a statement proved for all of them holds for K's.</> },
      ]}
    />
  )
}

// ---- 2. The definition as data -----------------------------------------------------------

export function DefinitionScene() {
  const panes: Pane[] = [
    { id: 'k', label: 'The K definition', source: peanoK },
    { id: 'c', label: 'The same definition as a Lean value', source: core },
    { id: 'o', label: 'Rule 1 as kompile emitted it (attributes omitted)', source: kore1 },
  ]
  const steps: Step[] = [
    { say: <>peano.k has one function, <code>pred</code>, and two rules on the k cell.</>, hl: { k: [lineOf(peanoK, 'rule pred(s(N)) => N'), lineOf(peanoK, 'rule pred(_) => z [owise]'), lineOf(peanoK, 'rule <k> run(s(N))'), lineOf(peanoK, 'rule <k> run(z)')] }, panes: ['k', 'c'] },
    { say: <><code>peanoCore</code> is that definition as one Lean value of type <code>Semantics</code>.</>, hl: { c: [lineOf(core, 'def peanoCore : Semantics :=')] }, panes: ['k', 'c'] },
    { say: <>Its user sorts, its four constructors with their argument and result sorts, and the one subsort <code>Nat &lt; Val</code>.</>, hl: { c: span(core, 'userSorts := ["Nat", "State", "Val"]', 'userSubsorts := [("Nat", "Val")]'), k: [lineOf(peanoK, 'syntax Val ::= Nat')] }, panes: ['k', 'c'] },
    { say: <><code>pred</code> has one clause, <code>pred(s(X0)) = X0</code>, and a catch-all clause, <code>pred(X0) = z</code>.</>, hl: { c: span(core, 'def predFn : Fn :=', 'owise := some'), k: [lineOf(peanoK, 'rule pred(s(N)) => N'), lineOf(peanoK, 'rule pred(_) => z [owise]')] }, panes: ['k', 'c'] },
    { say: <>Rule 1 as kompile emitted it: the subterm <code>s(N)</code> is shared under the name <code>Gen4</code>, and the counter cell is a variable.</>, hl: { o: [lineOf(kore1, "Lblrun{}(\\and{SortNat{}}(Lbls{}(VarN:SortNat{}), Var'Unds'Gen4:SortNat{}))"), lineOf(kore1, "Var'Unds'DotVar0:SortGeneratedCounterCell{}")] }, panes: ['c', 'o'] },
    { say: <>In Lean the sharing is the as-pattern <code>.as (ts (.var 0)) 1</code>, and the counter cell is <code>.var 2</code>.</>, hl: { c: [lineOf(core, 'lhs := tcfg (trun (.as (ts (.var 0)) 1)) (.var 2)')], o: [lineOf(kore1, "Lblrun{}(\\and{SortNat{}}(Lbls{}(VarN:SortNat{}), Var'Unds'Gen4:SortNat{}))")] }, panes: ['c', 'o'] },
    { say: <>The right-hand side calls <code>pred</code> on variable 1, the whole <code>s(N)</code>.</>, hl: { c: [lineOf(core, 'rhs := tcfg (trun (tpred (.var 1))) (.var 2)')], o: [lineOf(kore1, "inj{SortState{}, SortKItem{}}(Lblrun{}(Lblpred{}(Var'Unds'Gen4:SortNat{})))")] }, panes: ['c', 'o'] },
    { say: <>Rule 2 matches <code>run(z)</code> and writes <code>done(z)</code>, through the injection <code>inj{'{'}Nat,Val{'}'}</code> that the subsort <code>Nat &lt; Val</code> needs.</>, hl: { c: span(core, '-- <k> run(z #as Gen4) => done(Gen4) </k>', 'rhs := tcfg (tdone'), k: [lineOf(peanoK, 'rule <k> run(z)')] }, panes: ['k', 'c'] },
  ]
  return (
    <LessonScene
      title="The definition as data"
      panes={panes}
      steps={steps}
      visual={(at) =>
        at >= 4 && at <= 6 ? (
          <TermBox label="rule runSucc, left-hand side → right-hand side">
            <PatternView term={rules.runSucc.lhs} /> ⇒ <PatternView term={rules.runSucc.rhs} />
          </TermBox>
        ) : at === 7 ? (
          <TermBox label="rule runZero">
            <PatternView term={rules.runZero.lhs} /> ⇒ <PatternView term={rules.runZero.rhs} />
          </TermBox>
        ) : null
      }
      questions={[
        { q: 'Why does the k cell hold exactly one item in both rules?',
          a: <>The source rules have no <code>...</code>, so kompile matches <code>kseq(item, dotk)</code>: the item followed by the empty sequence, and nothing else.</> },
        { q: 'Where does the counter cell come from, if peano.k never mentions it?',
          a: <>From the configuration kompile generates, <code>&lt;generatedTop&gt; &lt;k&gt; … &lt;/k&gt; &lt;generatedCounter&gt; … &lt;/generatedCounter&gt;</code>. kompile turns each rule into a rule on that whole configuration, and the cells the rule does not mention become variables.</> },
      ]}
    />
  )
}

// ---- 3. Matching ---------------------------------------------------------------------------

export function MatchScene() {
  const σ = succ0.match ?? []
  const panes: Pane[] = [{ id: 'e', label: 'Matching', source: evaluation }]
  const rows: { mark?: readonly number[]; bound: number; say: ReactNode; hl: number[] }[] = [
    { bound: 0, say: <>A step starts by matching a rule's left-hand side against the configuration. Rule <code>runSucc</code> against <code>c0</code>:</>, hl: span(evaluation, 'def matchTerm (c : Semantics)', 'termination_by structural p => p') },
    { mark: [], bound: 0, say: <>A constructor pattern against a constructor term: the same symbol, so the arguments are matched in order and their substitutions joined.</>, hl: [lineOf(evaluation, '| .app f ps, .ctor g vs =>'), lineOf(evaluation, '| p :: ps, v :: vs => match matchTerm c p v')] },
    { mark: [0, 0, 0], bound: 0, say: <>The injection pattern meets an injection of the same sorts, <code>State</code> into <code>KItem</code>, so what is inside is matched.</>, hl: [lineOf(evaluation, ".inj a b p, .inj a' b' w =>"), lineOf(evaluation, "if a' = a then matchTerm c p w")] },
    { mark: [0, 0, 0, 0, 0], bound: 2, say: <>The as-pattern matches <code>s(X0)</code> against <code>s(z)</code>, binding X0 to <code>z</code>, and binds X1 to the whole <code>s(z)</code>.</>, hl: [lineOf(evaluation, '| .as p i, v =>'), lineOf(evaluation, '| .var i, v => some [(i, v)]')] },
    { mark: [1], bound: 3, say: <>The variable X2 binds the whole counter cell.</>, hl: [lineOf(evaluation, '| .var i, v => some [(i, v)]')] },
    { bound: 3, say: <>Lean's <code>matchTerm</code> on the real data gives exactly this σ: <code>{substText(σ)}</code>.</>, hl: span(evaluation, 'def matchTerm (c : Semantics)', 'termination_by structural p => p') },
    { bound: 0, say: <>Rule <code>runZero</code> needs <code>z</code> where <code>c0</code> has <code>s(z)</code>: different symbols, so <code>matchTerm</code> is <code>none</code> and the rule does not apply.</>, hl: [lineOf(evaluation, '| .app f ps, .ctor g vs =>')] },
    { bound: 3, say: <>Matching never looks at the sorts of variables; sorts are checked once, on the configuration, by <code>sortOf</code>.</>, hl: [lineOf(evaluation, '| .var i, v => some [(i, v)]')] },
  ]
  const patternMark: (readonly number[] | undefined)[] = [undefined, [], [0, 0, 0], [0, 0, 0, 0, 0], [1], undefined, undefined, undefined]
  return (
    <LessonScene
      title="Matching gives the substitution σ"
      panes={panes}
      steps={rows.map((r) => ({ say: r.say, hl: { e: r.hl } }))}
      visual={(at) => (
        <>
          <TermBox label={at === 6 ? 'pattern of runZero' : 'pattern of runSucc'}>
            <PatternView term={at === 6 ? rules.runZero.lhs : rules.runSucc.lhs} mark={at === 6 ? [0, 0, 0, 0, 0] : patternMark[at]} />
          </TermBox>
          <TermBox label="c0">
            <GroundView term={c0.term} mark={at === 6 ? [0, 0, 0, 0, 0] : rows[at].mark} />
          </TermBox>
          {at === 6 ? (
            <div className={styles.subst}><span className={styles.termLabel}>matchTerm =</span> none</div>
          ) : (
            <SubstView σ={σ} count={rows[at].bound} />
          )}
        </>
      )}
      questions={[
        { q: <>A pattern <code>inj{'{'}Val,KItem{'}'}(V)</code> meets the term <code>inj{'{'}Nat,KItem{'}'}(z)</code>. Does it match, and what is V bound to?</>,
          a: <>It matches, because <code>Nat &lt; Val</code>: the third branch of the injection case binds V to <code>inj{'{'}Nat,Val{'}'}(z)</code>, which denotes the same element. That is K's subsort semantics: a pattern of sort <code>Val</code> matches every term of a sort below <code>Val</code>. peano's two rules never need it.</> },
        { q: 'Why is there at most one σ?',
          a: <><code>matchTerm</code> is a function, so it has one result. That this result is the only substitution that works also needs linear patterns, which a well-formed definition has.</> },
      ]}
    />
  )
}

// ---- 4. Evaluating the right-hand side -------------------------------------------------------

type Row = { depth: number; tag: Explain['rule'] | 'clause' | 'owise'; text: string; value: string; key: string }

function flatten(node: Explain, depth = 0, out: Row[] = [], key = 'r'): Row[] {
  out.push({ depth, tag: node.rule, text: patternText(node.term), value: node.value ? groundText(node.value) : 'no value', key })
  node.children?.forEach((child, i) => flatten(child, depth + 1, out, `${key}.${i}`))
  const call = node.call
  if (call?.rhs) {
    const σ = substText(call.subst ?? [])
    out.push({
      depth: depth + 1,
      tag: call.by === 'owise' ? 'owise' : 'clause',
      text: call.by === 'owise' ? `catch-all clause, with ${σ}` : `clause ${call.clause} matches ${(call.args ?? []).map(groundText).join(', ')} with ${σ}`,
      value: '',
      key: `${key}.call`,
    })
    flatten(call.rhs, depth + 2, out, `${key}.call.rhs`)
  }
  return out
}

const tagClass: Record<Row['tag'], string> = {
  ctor: styles.ctorTag, call: styles.callTag, var: styles.varTag, inj: styles.injTag, as: styles.injTag, clause: styles.callTag, owise: styles.callTag,
}

function EvalTree({ rows, on }: { rows: Row[]; on: (row: Row) => boolean | undefined }) {
  return (
    <div className={styles.tree}>
      {rows.map((row) => {
        const lit = on(row)
        return (
          <div key={row.key} className={`${styles.treeRow} ${lit ? styles.on : lit === false ? styles.off : ''}`} style={{ paddingLeft: `${row.depth * 0.9 + 0.3}rem` }}>
            <span className={tagClass[row.tag]}>{row.tag}</span>
            <span>
              {row.text}
              {row.value && <span className={styles.small}> = {row.value}</span>}
            </span>
          </div>
        )
      })}
    </div>
  )
}

export function EvaluationScene() {
  const rows = flatten(succ0.rhs!)
  const owiseRows = flatten(predOf('z').explain)
  const panes: Pane[] = [{ id: 'e', label: 'The evaluation relation', source: evaluation }]
  const has = (tag: Row['tag'], text?: string) => (row: Row) => row.tag === tag && (text === undefined || row.text.startsWith(text))
  const steps: (Step & { on?: (row: Row) => boolean; owise?: boolean })[] = [
    { say: <>Under σ, rule 1's right-hand side is a term to evaluate: <code>EvalTerm c σ t v</code> says that <code>t</code> has the value <code>v</code>.</>, hl: { e: span(evaluation, 'inductive EvalTerm (c : Semantics)', 'EvalTerm c σ (.inj a b t) (injNormal a b v)') } },
    { say: <>A head that is a constructor of peano builds the constructor term: <code>EvalTerm.ctor</code>.</>, hl: { e: span(evaluation, '| ctor {σ : Subst} {f : String}', 'EvalTerm c σ (.app f ts) (.ctor f vs)') }, on: has('ctor') },
    { say: <>A variable is its value in σ: X2 is the counter cell, X1 is <code>s(z)</code>.</>, hl: { e: [lineOf(evaluation, '| var {σ : Subst} {i : Nat}')] }, on: (row) => row.tag === 'var' && !row.key.includes('call.rhs') },
    { say: <><code>pred</code> is no constructor, so <code>pred(X1)</code> is a function call: <code>EvalTerm.call</code>, whose value is given by <code>Eval</code>.</>, hl: { e: span(evaluation, '| call {σ : Subst}', '(hf : Eval c f vs v) : EvalTerm c σ (.app f ts) v') }, on: has('call') },
    { say: <><code>Eval.clause</code>: the first clause whose patterns match the arguments decides. Clause 0, <code>pred(s(X0))</code>, matches <code>s(z)</code> with X0 ↦ z.</>, hl: { e: span(evaluation, '| clause {f : String}', '(hrhs : EvalTerm c σ cl.rhs v) : Eval c f vs v') }, on: has('clause') },
    { say: <>Its right-hand side, X0, has the value <code>z</code> under that σ, so <code>pred(s(z))</code> has the value <code>z</code>.</>, hl: { e: [lineOf(evaluation, '(hrhs : EvalTerm c σ cl.rhs v) : Eval c f vs v')] }, on: (row) => row.key.endsWith('call.rhs') },
    { say: <>No clause before the deciding one may match. If the deciding clause's right-hand side had no value, <code>pred</code> would have none there: no later clause is tried.</>, hl: { e: [lineOf(evaluation, "(hpre : ∀ cl' ∈ pre, matchTerms c cl'.pats vs = none)"), lineOf(evaluation, '(hmatch : matchTerms c cl.pats vs = some σ)')] }, on: has('clause') },
    { say: <><code>Eval.owise</code> applies exactly where no clause matches: Lean computes <code>pred(z)</code> as <code>z</code> by the catch-all clause.</>, hl: { e: span(evaluation, '| owise {f : String}', '(hrhs : EvalTerm c (argSubst 0 vs) o.rhs v) : Eval c f vs v') }, owise: true },
    { say: <>The injection is kept in normal form, and the whole right-hand side has the value <code>{kc(c1.term)}</code> in the k cell: the configuration <code>c1</code>.</>, hl: { e: span(evaluation, '| inj {σ : Subst} {a b : String}', 'EvalTerm c σ (.inj a b t) (injNormal a b v)') }, on: (row) => row.key === 'r' || row.tag === 'inj' },
  ]
  return (
    <LessonScene
      title="Evaluating the right-hand side"
      panes={panes}
      steps={steps}
      visual={(at) => {
        const s = steps[at]
        return s.owise ? (
          <TermBox label="pred(z), computed"><EvalTree rows={owiseRows} on={() => undefined} /></TermBox>
        ) : (
          <TermBox label={`right-hand side of runSucc under ${substText(succ0.match ?? [])}`}>
            <EvalTree rows={rows} on={(row) => (s.on ? s.on(row) : undefined)} />
          </TermBox>
        )
      }}
      questions={[
        { q: <>What value does <code>Eval</code> give <code>pred(\dv{'{'}Int{'}'}("5"))</code>?</>,
          a: <><code>z</code>, by the catch-all clause: the pattern <code>s(X0)</code> does not match a domain value. Lean computes the same. <code>Eval</code> is defined on every ground term, not only on terms of sort <code>Nat</code>, so the equations of <code>pred</code> hold more widely than K's.</> },
        { q: 'If the deciding clause had a right-hand side without a value, could a later clause give one?',
          a: <>No. The KORE equations' premises read the arguments only, so the clause that matches decides; with no value there, the function has no value at those arguments.</> },
        { q: <>Can <code>Eval</code> run forever on a function that never terminates?</>,
          a: <>It does not run at all: it is an inductive relation, so a value exists only with a finite derivation. A function that does not terminate at some arguments has no value there.</> },
      ]}
    />
  )
}

// ---- 5. The step, three times ------------------------------------------------------------------

export function StepScene() {
  const panes: Pane[] = [{ id: 's', label: 'One rewrite step', source: step }]
  const nodes = [c0, c1, c2]
  const steps: (Step & { on: number[]; arrows: number[] })[] = [
    { say: <><code>Step</code> has one constructor: a rule of the definition, the σ its match gives, and the value of its right-hand side under σ.</>, hl: { s: span(step, 'inductive Step (c : Semantics)', '(heval : EvalTerm c σ r.rhs y.val) : Step c x y') }, on: [], arrows: [] },
    { say: <>From <code>c0</code>, rule <code>runSucc</code> matches with σ, and its right-hand side has the value <code>c1</code>: <code>Step c0 c1</code>.</>, hl: { s: [lineOf(step, '(hmatch : matchTerm c r.lhs x.val = some σ)'), lineOf(step, '(heval : EvalTerm c σ r.rhs y.val)')] }, on: [0, 1], arrows: [0] },
    { say: <><code>runZero</code> does not match <code>c0</code>, so <code>c0</code> has one successor; the executable step lists exactly <code>[c1]</code>.</>, hl: { s: [lineOf(step, '| rule {x y : Config c} (r : Rule) (mem : r ∈ c.rules)')] }, on: [0], arrows: [0] },
    { say: <>From <code>c1</code>, <code>runZero</code> matches with <code>{substText(zero1.match ?? [])}</code> and writes <code>{kc(c2.term)}</code>: <code>Step c1 c2</code>.</>, hl: { s: [lineOf(step, '(hmatch : matchTerm c r.lhs x.val = some σ)'), lineOf(step, '(heval : EvalTerm c σ r.rhs y.val)')] }, on: [1, 2], arrows: [1] },
    { say: <>From <code>c2</code> neither rule matches, and the executable step lists no successor: <code>done(z)</code> is stuck, which is how this run ends.</>, hl: { s: [lineOf(step, '| rule {x y : Config c} (r : Rule) (mem : r ∈ c.rules)')] }, on: [2], arrows: [] },
    { say: <>Both ends range over <code>Config c</code>: a right-hand side whose value is not of the configuration sort gives no step.</>, hl: { s: [lineOf(step, 'inductive Step (c : Semantics) : Config c → Config c → Prop where')] }, on: [0, 1, 2], arrows: [0, 1] },
  ]
  return (
    <LessonScene
      title="run(s(z)) → run(z) → done(z)"
      panes={panes}
      steps={steps}
      visual={(at) => {
        const s = steps[at]
        const labels = ['runSucc', 'runZero']
        return (
          <div className={styles.chain}>
            {nodes.map((node, i) => (
              <div key={node.name} style={{ display: 'contents' }}>
                <div className={`${styles.node} ${s.on.includes(i) ? styles.on : s.on.length ? styles.off : ''} ${i === 2 ? styles.stuck : ''}`}>
                  <span className={styles.termLabel}>{node.name}: k cell</span>
                  <code>{kc(node.term)}</code>
                  <span className={styles.small}>successors: {node.successors?.length ?? 0}</span>
                </div>
                {i < 2 && (
                  <div className={styles.arrow}>
                    {labels[i]}
                    <br />
                    {s.arrows.includes(i) ? '⟶' : '⇢'}
                  </div>
                )}
              </div>
            ))}
          </div>
        )
      }}
      questions={[
        { q: <>The equations of <code>pred</code> apply inside terms. Does <code>Step</code> apply a rule inside a term too?</>,
          a: <>No, and it need not: kompile has already made each rule a rule on the whole configuration, with the other cells as variables, so a step at the top is K's step. These definitions have no <code>requires</code>, <code>ensures</code> or priorities; no field of a rule holds them.</> },
        { q: <>Which configuration does <code>Step</code> relate to nothing, and which statement of the next lesson relies on it?</>,
          a: <><code>c2</code>, with <code>done(z)</code> in the k cell. The witness <code>stuck_done</code> proves it has no successor, which shows that <code>Step</code> does not relate every configuration to something.</> },
      ]}
    />
  )
}

// ---- 6. Where the executable evaluator lives ---------------------------------------------------

export function FuelScene() {
  const fuel = source('evalWithFuel')
  const fnFuel = source('fnFuel')
  const iff = source('stepIff')
  const ready = source('evalReady')
  const iffWf = source('stepIffWf')
  const checks = source('LibraryChecks')
  const panes: Pane[] = [
    { id: 'e', label: 'The frozen relation', source: evaluation },
    { id: 'f', label: 'The executable evaluator (checked layer)', source: fuel },
    { id: 'n', label: 'Its fuel', source: fnFuel },
    { id: 'i', label: 'What ties them', source: iff },
    { id: 'r', label: 'The condition', source: ready },
    { id: 'p', label: 'On peano', source: checks },
    { id: 'w', label: 'Under wf alone', source: iffWf },
  ]
  const steps: Step[] = [
    { say: <>The frozen layer has no fuel: <code>Eval</code> is a relation, and <code>Step</code> reads it.</>, hl: { e: span(evaluation, 'There is no fuel and no termination argument', 'relation for the definitions it accepts') }, panes: ['e'] },
    { say: <>To compute a step, <code>Execution.lean</code> has <code>evalWithFuel</code>: each self call gets one unit less, and at zero the value is <code>none</code>.</>, hl: { f: span(fuel, 'def evalWithFuel', '| n + 1, vs =>') }, panes: ['f', 'n'] },
    { say: <>A call starts with <code>Fn.fuel</code>: one more than the size of the argument at the position where every self call shrinks.</>, hl: { n: span(fnFuel, 'def Fn.fuel', '| none => 0) + 1') }, panes: ['f', 'n'] },
    { say: <>Lean's kernel does not reduce well-founded recursion, so explicit fuel is what lets the kernel run the evaluator on closed terms.</>, hl: { f: [lineOf(fuel, '| 0, _ => none')] }, panes: ['f', 'n'] },
    { say: <><code>step_iff</code>: <code>Step c x y ↔ y ∈ successors c x</code>, proved once, for every definition that <code>evalReady</code> accepts.</>, hl: { i: [lineOf(iff, 'theorem step_iff (hr : c.evalReady = true)'), lineOf(iff, 'theorem eval_iff (hr : c.evalReady = true)')] }, panes: ['i', 'r'] },
    { say: <><code>evalReady</code> is a check on the data: distinct labels, fuel that suffices, no call of a later function.</>, hl: { r: span(ready, 'def Semantics.evalReady', 'nodup (c.fns.map') }, panes: ['i', 'r'] },
    { say: <>For peano the kernel decides it: <code>evalReady_peano</code>, so peano's executable step is its frozen step.</>, hl: { p: [lineOf(checks, 'theorem evalReady_peano'), lineOf(checks, 'theorem step_iff_peano')] }, panes: ['p'] },
    { say: <><code>step_iff_wf</code> gives the same for any definition that is well formed, with no further check.</>, hl: { w: span(iffWf, 'theorem step_iff_wf', 'step_iff (wf_evalReady') }, panes: ['w'] },
  ]
  return (
    <LessonScene
      title="Where the fuel went"
      panes={panes}
      steps={steps}
      questions={[
        { q: 'Why not define the step with the fueled evaluator directly?',
          a: <>Then what a step means would depend on a fuel bound, an arbitrary cutoff inside the meaning of every statement. With the relation, that the fuel always suffices is a theorem, proved once (<code>Eval.complete</code>), not a choice a reader has to review.</> },
        { q: <>If <code>evalWithFuel</code> had a bug, could a wrong statement about <code>Step</code> be proved?</>,
          a: <>No. Statements mention <code>Step</code>, not <code>successors</code>. A wrong evaluator would make <code>step_iff</code> unprovable, and a proof that used it would not check.</> },
      ]}
    />
  )
}
