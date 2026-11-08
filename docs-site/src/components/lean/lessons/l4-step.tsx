'use client'

// Lesson 4: peano's run(s(z)) → run(z) → done(z), on the real definitions. Terms, substitutions,
// values and successors are the ones Lean computed on peanoCore (the generator's Facts.lean); source
// panes are the files at the recorded commit.

import { type Explain, config, groundText, kItem, koreAxiom, lean, lineOf, patternText, peanoK, ruleFact, source, span, substText } from '../data'
import { type Lesson, note } from '../lesson'
import { A, Arrow, Box, courseStyles as styles, groundTree, Label, patternTree, Small, Svg, TextBox, Tree, varClass } from '../viz'

const value = source('Value')
const evaluation = source('Evaluation')
const step = source('Step')
const core = source('PeanoCore')
const k = peanoK
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

const files = ['FixedSignature', 'Core', 'Value', 'Evaluation', 'Step']
const fileRole = ['sorts and constructors every kompiled definition has', 'what a definition is', 'configurations', 'matching and evaluation', 'one step']

const fiveFiles = (at: number) => (
  <Svg viewBox="0 0 900 420" label="The five files that define a step, each importing the ones before">
    {files.map((f, i) => (
      <g key={f}>
        <Box x={390} y={50 + i * 78} w={240} text={`${f}.lean`} />
        <Label x={525} y={55 + i * 78} text={fileRole[i]} tone="var(--muted)" size={13} />
        {i < 4 && <Arrow x1={390} y1={66 + i * 78} x2={390} y2={112 + i * 78} on={at === 1} />}
      </g>
    ))}
    <A show={at >= 1}>
      <Label x={130} y={200} anchor="middle" size={13} weight={600} text="imports only Init" />
      <Label x={130} y={220} anchor="middle" size={13} weight={600} text="and each other" />
      <Label x={130} y={250} anchor="middle" size={12} tone="var(--muted)" text="no instance, notation or macro" />
      <Label x={130} y={270} anchor="middle" size={12} tone="var(--muted)" text="every function total and structural" />
    </A>
  </Svg>
)

// ---- a configuration as a tree ------------------------------------------------------------------

const tree0 = groundTree(c0.term)
const configLit: (readonly string[])[] = [[], [], ['r.0.0.0.0'], ['r.0.0.0'], ['r.1.0'], [], [], ['r'], []]

const configTree = (at: number) => (
  <Svg viewBox="0 0 520 390" label={`The configuration ${groundText(c0.term)} as a tree`}>
    <Tree node={tree0} x={0} y={30} w={520} dy={55} lit={configLit[at]} />
  </Svg>
)

// ---- matching: the pattern and the term, side by side -------------------------------------------

const σ = succ0.match ?? []
const patSucc = patternTree(rules.runSucc.lhs)
const patZero = patternTree(rules.runZero.lhs)
const matchFrames: { pat: readonly string[]; term: readonly string[]; bound: number }[] = [
  { pat: [], term: [], bound: 0 },
  { pat: ['r'], term: ['r'], bound: 0 },
  { pat: ['r.0.0.0'], term: ['r.0.0.0'], bound: 0 },
  { pat: ['r.0.0.0.0.0', 'r.0.0.0.0.0.0', 'r.0.0.0.0.0.0.0'], term: ['r.0.0.0.0.0', 'r.0.0.0.0.0.0'], bound: 2 },
  { pat: ['r.1'], term: ['r.1', 'r.1.0'], bound: 3 },
  { pat: [], term: [], bound: 3 },
  { pat: ['r.0.0.0.0.0', 'r.0.0.0.0.0.0'], term: ['r.0.0.0.0.0'], bound: 0 },
  { pat: ['r.1'], term: [], bound: 3 },
]

const matching = (at: number) => {
  const m = matchFrames[at]
  const zero = at === 6
  return (
    <>
      <Svg viewBox="0 0 740 440" label="The rule's left-hand side as a tree beside the configuration's tree">
        <Label x={180} y={18} anchor="middle" size={11} tone="var(--muted)" isMono text={zero ? 'PATTERN OF RUNZERO' : 'PATTERN OF RUNSUCC'} />
        <Label x={560} y={18} anchor="middle" size={11} tone="var(--muted)" isMono text="THE TERM C0" />
        <Tree key={zero ? 'zero' : 'succ'} node={zero ? patZero : patSucc} x={0} y={48} w={360} dy={52} lit={m.pat} />
        <Tree node={tree0} x={380} y={48} w={360} dy={52} lit={m.term} />
      </Svg>
      {zero ? (
        <TextBox label="matchTerm">none: different symbols, so the rule does not apply</TextBox>
      ) : (
        <TextBox label="σ, as matching binds it">
          {m.bound === 0 ? <Small>nothing bound yet</Small> : σ.slice(0, m.bound).map((b, i) => (
            <span key={b.var}>{i > 0 && ',  '}<span className={varClass(b.var)}>X{b.var}</span> ↦ {groundText(b.value)}</span>
          ))}
        </TextBox>
      )}
    </>
  )
}

// ---- evaluating a right-hand side -----------------------------------------------------------------

type Row = { depth: number; tag: Explain['rule'] | 'clause' | 'owise'; text: string; value: string; key: string }

function flatten(node: Explain, depth = 0, out: Row[] = [], key = 'r'): Row[] {
  out.push({ depth, tag: node.rule, text: patternText(node.term), value: node.value ? groundText(node.value) : 'no value', key })
  node.children?.forEach((child, i) => flatten(child, depth + 1, out, `${key}.${i}`))
  const call = node.call
  if (call?.rhs) {
    const sub = substText(call.subst ?? [])
    out.push({
      depth: depth + 1,
      tag: call.by === 'owise' ? 'owise' : 'clause',
      text: call.by === 'owise' ? `catch-all clause, with ${sub}` : `clause ${call.clause} matches ${(call.args ?? []).map(groundText).join(', ')} with ${sub}`,
      value: '',
      key: `${key}.call`,
    })
    flatten(call.rhs, depth + 2, out, `${key}.call.rhs`)
  }
  return out
}

const tagTone: Record<Row['tag'], string> = { ctor: 'var(--accent)', call: 'var(--gold)', var: 'var(--v2)', inj: 'var(--alt)', as: 'var(--alt)', clause: 'var(--gold)', owise: 'var(--gold)' }

function EvalTree({ rows, on }: { rows: Row[]; on: (row: Row) => boolean | undefined }) {
  return (
    <div className={styles.tree}>
      {rows.map((row) => {
        const lit = on(row)
        return (
          <div key={row.key} className={`${styles.treeRow} ${lit ? styles.lit : lit === false ? styles.dim : ''}`} style={{ paddingLeft: `${row.depth * 0.9 + 0.3}rem` }}>
            <span style={{ color: tagTone[row.tag], fontWeight: 600, minWidth: '3.2em' }}>{row.tag}</span>
            <span>{row.text}{row.value && <span className={styles.small}> = {row.value}</span>}</span>
          </div>
        )
      })}
    </div>
  )
}

const evalRows = flatten(succ0.rhs!)
const owiseRows = flatten(predOf('z').explain)
const has = (tag: Row['tag']) => (row: Row) => row.tag === tag
const evalOn: ((row: Row) => boolean)[] = [
  () => true,
  has('ctor'),
  (row) => row.tag === 'var' && !row.key.includes('call.rhs'),
  has('call'),
  has('clause'),
  (row) => row.key.endsWith('call.rhs'),
  has('clause'),
  () => true,
  (row) => row.key === 'r' || row.tag === 'inj',
]
const evalAt = (at: number) => (
  <TextBox label={at === 7 ? 'pred(z), computed' : 'right-hand side of runSucc, under σ'}>
    {at === 7 ? <EvalTree rows={owiseRows} on={() => undefined} /> : <EvalTree rows={evalRows} on={(row) => (at === 0 ? undefined : evalOn[at](row))} />}
  </TextBox>
)

// ---- the step, three times --------------------------------------------------------------------------

const stepStates: { on: number[]; arrows: number[] }[] = [
  { on: [], arrows: [] },
  { on: [0, 1], arrows: [0] },
  { on: [0], arrows: [0] },
  { on: [1, 2], arrows: [1] },
  { on: [2], arrows: [] },
  { on: [0, 1, 2], arrows: [0, 1] },
]
const stepChain = (at: number) => {
  const st = stepStates[at]
  const nodes = [c0, c1, c2]
  const names = ['runSucc', 'runZero']
  return (
    <Svg viewBox="0 0 900 170" label="c0 steps to c1 by runSucc, c1 steps to c2 by runZero, and c2 is stuck">
      {nodes.map((node, i) => (
        <g key={node.name}>
          <Box x={140 + i * 310} y={70} w={220} text={kc(node.term).replace(/inj\{[^}]*\}\((.*)\)\)$/, '$1)')} sub={`${node.name}, successors: ${node.successors?.length ?? 0}`} tone={st.on.includes(i) ? 'on' : 'plain'} />
          {i < 2 && <Arrow x1={252 + i * 310} y1={70} x2={338 + i * 310} y2={70} label={names[i]} on={st.arrows.includes(i)} dash={!st.arrows.includes(i)} />}
        </g>
      ))}
      <A show={at === 4}><Label x={760} y={124} anchor="middle" size={13} weight={600} tone="var(--bad)" text="stuck" /></A>
    </Svg>
  )
}

const fuel = source('evalWithFuel')
const fnFuel = source('fnFuel')
const iff = source('stepIff')
const ready = source('evalReady')
const iffWf = source('stepIffWf')
const checks = source('LibraryChecks')

export const lesson4: Lesson = {
  id: 'what-a-step-means',
  number: 4,
  title: 'What a step means in Lean',
  scenes: [
    {
      id: 's1',
      title: 'Five files, read once',
      visual: fiveFiles,
      frames: [
        { say: "`run(s(z))` steps to `run(z)` under peano's first rule. To rely on that, you need to know which terms are configurations, when a rule applies, what its right-hand side evaluates to, and what happens when a function has no value. For every K definition, that meaning is in ==five Lean files==." },
        { say: "They import nothing but Lean's `Init` and each other, and they declare no instance, notation or macro. Every function in them is total and structurally recursive. Lesson 6 counts what in them a reader must read." },
      ],
    },
    {
      id: 's2',
      title: 'A configuration is a tree',
      visual: configTree,
      panes: [{ id: 'v', label: 'Ground terms and their sorts', source: value }],
      frames: [
        { say: "This is the configuration you'll run: `run(s(z))` in the k cell, and the counter cell that krust's initial configuration has." },
        { hl: { v: span(value, 'inductive GroundTerm where', 'deriving Repr, Inhabited') }, notes: [note('v', lineOf(value, 'inductive GroundTerm where'), "A plain tree with three kinds of node.")], say: "In Lean it is a `GroundTerm`." },
        { hl: { v: [lineOf(value, '| ctor (f : String)')] }, notes: [note('v', lineOf(value, '| ctor (f : String)'), "A constructor applied to arguments, named by its KORE symbol: `s` is `Lbls`, `<k>` is `Lbl'-LT-'k'-GT-'`.")] },
        { hl: { v: [lineOf(value, '| inj (a b : String) (t : GroundTerm)')] }, notes: [note('v', lineOf(value, '| inj (a b : String) (t : GroundTerm)'), "An injection along a subsort: `inj{State,KItem}` puts a `State` where the K sequence expects a `KItem`.")], say: "Subsorting is explicit, as in KORE." },
        {
          hl: { v: [lineOf(value, '| dv (s : String) (lit : String)')] },
          notes: [note('v', lineOf(value, '| dv (s : String) (lit : String)'), "A domain value of a builtin sort: the counter's 0 is `\\dv{Int}(\"0\")`.")],
          ask: {
            q: "Is `\\dv{Int}(\"abc\")` a value of sort `Int`?",
            options: ["No, the literal must parse as a number", "Yes: any literal string is accepted as a domain value of a base sort", "Only inside a counter cell"],
            answer: 1,
            why: "The configurations are therefore a superset of K's, and a statement proved for all of them holds for K's.",
          },
        },
        { hl: { v: span(value, 'def sortOf : GroundTerm → Option String', 'termination_by structural t => t') }, notes: [note('v', lineOf(value, 'def sortOf : GroundTerm → Option String'), "Computes a tree's sort from the definition's data, or `none`.")], say: "The type says nothing about sorts." },
        { hl: { v: [lineOf(value, '| some k => if sortsOf ts == some k.args'), lineOf(value, '| .inj a b t => if c.subsorts.contains (a, b)')] }, notes: [note('v', lineOf(value, '| some k => if sortsOf ts == some k.args'), "A constructor must be declared and get exactly its argument sorts."), note('v', lineOf(value, '| .inj a b t => if c.subsorts.contains (a, b)'), "An injection must follow a declared subsort and must not sit directly on another injection.")] },
        { hl: { v: [...span(value, 'def Value (c : Semantics)', 'def Value (c : Semantics)'), lineOf(value, 'abbrev Config (c : Semantics)')] }, say: "Lean computes `sortOf` of this tree as `" + c0.sort + "`, so it's a `Config`: a value of the configuration sort." },
        { say: "Because an injection never sits directly on another, each element has one representation. So ==equality of configurations is equality of trees==." },
      ],
    },
    {
      id: 's3',
      title: 'The definition as data',
      panes: [
        { id: 'k', label: 'The K definition', source: k, lang: 'k' },
        { id: 'c', label: 'The same definition as a Lean value', source: core },
      ],
      frames: [
        { hl: { k: [lineOf(k, 'rule pred(s(N)) => N'), lineOf(k, 'rule pred(_) => z [owise]'), lineOf(k, 'rule <k> run(s(N))'), lineOf(k, 'rule <k> run(z)')] }, notes: [note('k', lineOf(k, 'rule pred(s(N)) => N'), "One function, `pred`."), note('k', lineOf(k, 'rule <k> run(s(N))'), "Two rules on the k cell.")] },
        { hl: { c: [lineOf(core, 'def peanoCore : Semantics :=')] }, notes: [note('c', lineOf(core, 'def peanoCore : Semantics :='), "That definition, as one Lean value of type `Semantics`.")] },
        { hl: { c: span(core, 'userSorts := ["Nat", "State", "Val"]', 'userSubsorts := [("Nat", "Val")]'), k: [lineOf(k, 'syntax Val ::= Nat')] }, notes: [note('c', lineOf(core, 'userSorts := ["Nat", "State", "Val"]'), "Its user sorts, its four constructors with their argument and result sorts, and the one subsort `Nat < Val`.")] },
        { hl: { c: span(core, 'def predFn : Fn :=', 'owise := some'), k: [lineOf(k, 'rule pred(s(N)) => N'), lineOf(k, 'rule pred(_) => z [owise]')] }, notes: [note('c', lineOf(core, 'def predFn : Fn :='), "One clause, `pred(s(X0)) = X0`, and a catch-all clause, `pred(X0) = z`.")] },
      ],
    },
    {
      id: 's4',
      title: 'The first rule, in both forms',
      panes: [
        { id: 'c', label: 'The Lean value', source: core },
        { id: 'o', label: 'Rule 1 as kompile emitted it', source: kore1, lang: 'kore' },
      ],
      frames: [
        { hl: { o: [lineOf(kore1, "Lblrun{}(\\and{SortNat{}}(Lbls{}(VarN:SortNat{}), Var'Unds'Gen4:SortNat{}))"), lineOf(kore1, "Var'Unds'DotVar0:SortGeneratedCounterCell{}")] }, notes: [note('o', lineOf(kore1, "Lblrun{}(\\and{SortNat{}}(Lbls{}(VarN:SortNat{}), Var'Unds'Gen4:SortNat{}))"), "The subterm `s(N)` is shared under the name `Gen4`.", "Var'Unds'Gen4"), note('o', lineOf(kore1, "Var'Unds'DotVar0:SortGeneratedCounterCell{}"), "The counter cell is a variable.", "Var'Unds'DotVar0")] },
        { hl: { c: [lineOf(core, 'lhs := tcfg (trun (.as (ts (.var 0)) 1)) (.var 2)')], o: [lineOf(kore1, "Lblrun{}(\\and{SortNat{}}(Lbls{}(VarN:SortNat{}), Var'Unds'Gen4:SortNat{}))")] }, notes: [note('c', lineOf(core, 'lhs := tcfg (trun (.as (ts (.var 0)) 1)) (.var 2)'), "The sharing is an as-pattern…", '.as (ts (.var 0)) 1'), note('c', lineOf(core, 'lhs := tcfg (trun (.as (ts (.var 0)) 1)) (.var 2)'), "…and the counter cell is variable 2.", '(.var 2)')] },
        { hl: { c: [lineOf(core, 'rhs := tcfg (trun (tpred (.var 1))) (.var 2)')], o: [lineOf(kore1, "inj{SortState{}, SortKItem{}}(Lblrun{}(Lblpred{}(Var'Unds'Gen4:SortNat{})))")] }, notes: [note('c', lineOf(core, 'rhs := tcfg (trun (tpred (.var 1))) (.var 2)'), "Calls `pred` on variable 1, the whole `s(N)`.", 'tpred (.var 1)')] },
      ],
    },
    {
      id: 's5',
      title: 'The second rule, and the check',
      panes: [
        { id: 'k', label: 'The K definition', source: k, lang: 'k' },
        { id: 'c', label: 'The Lean value', source: core },
      ],
      frames: [
        { hl: { c: span(core, '-- <k> run(z #as Gen4) => done(Gen4) </k>', 'rhs := tcfg (tdone'), k: [lineOf(k, 'rule <k> run(z)')] }, notes: [note('c', lineOf(core, '-- <k> run(z #as Gen4) => done(Gen4) </k>'), "Matches `run(z)` and writes `done(z)`, through the injection `inj{Nat,Val}` that the subsort `Nat < Val` needs.")] },
        { say: "You don't have to take the translation on trust. Lean generates KORE from this value, and the kernel checks it equals what kompile produced for `peano.k`, sentence for sentence. That's lesson 3's round trip." },
      ],
    },
    {
      id: 's6',
      title: 'Matching gives the substitution σ',
      visual: matching,
      arrange: 'wide',
      panes: [{ id: 'e', label: 'Matching', source: evaluation }],
      frames: [
        { hl: { e: span(evaluation, 'def matchTerm (c : Semantics)', 'termination_by structural p => p') }, say: "A step starts by matching a rule's left-hand side against the configuration. Here is rule `runSucc` against `c0`." },
        { hl: { e: [lineOf(evaluation, '| .app f ps, .ctor g vs =>'), lineOf(evaluation, '| p :: ps, v :: vs => match matchTerm c p v')] }, notes: [note('e', lineOf(evaluation, '| .app f ps, .ctor g vs =>'), "The same symbol, so the arguments are matched in order and their substitutions joined.")], say: "A constructor pattern against a constructor term." },
        { hl: { e: [lineOf(evaluation, ".inj a b p, .inj a' b' w =>"), lineOf(evaluation, "if a' = a then matchTerm c p w")] }, notes: [note('e', lineOf(evaluation, ".inj a b p, .inj a' b' w =>"), "The same sorts, `State` into `KItem`, so what's inside is matched.")], say: "The injection pattern meets an injection." },
        { hl: { e: [lineOf(evaluation, '| .as p i, v =>'), lineOf(evaluation, '| .var i, v => some [(i, v)]')] }, notes: [note('e', lineOf(evaluation, '| .as p i, v =>'), "Matches `s(X0)` against `s(z)`, binding X0 to `z`, and binds X1 to the whole `s(z)`.", '.as p i, v')] },
        { hl: { e: [lineOf(evaluation, '| .var i, v => some [(i, v)]')] }, notes: [note('e', lineOf(evaluation, '| .var i, v => some [(i, v)]'), "The variable X2 binds the whole counter cell.", '.var i, v')] },
        {
          hl: { e: span(evaluation, 'def matchTerm (c : Semantics)', 'termination_by structural p => p') },
          say: "Lean's `matchTerm` on the real data gives exactly this σ.",
          ask: {
            q: "Why is there at most one σ?",
            options: ["`matchTerm` is a function, so it has one result", "Rules are checked to have one variable", "Because configurations have one k cell"],
            answer: 0,
            why: "That this result is the only substitution that works also needs linear patterns, which a well-formed definition has.",
          },
        },
        { hl: { e: [lineOf(evaluation, '| .app f ps, .ctor g vs =>')] }, notes: [note('e', lineOf(evaluation, '| .app f ps, .ctor g vs =>'), "`z` where `c0` has `s(z)`: different symbols, so `matchTerm` is `none`.", '.app f ps, .ctor g vs')], say: "Rule `runZero` does not apply." },
        { hl: { e: [lineOf(evaluation, '| .var i, v => some [(i, v)]')] }, say: "Matching ==never looks at the sorts of variables==. Sorts are checked once, on the configuration, by `sortOf`." },
      ],
    },
    {
      id: 's7',
      title: 'Evaluating the right-hand side',
      visual: evalAt,
      panes: [{ id: 'e', label: 'The evaluation relation', source: evaluation }],
      frames: [
        { hl: { e: span(evaluation, 'inductive EvalTerm (c : Semantics)', 'EvalTerm c σ (.inj a b t) (injNormal a b v)') }, say: "A K function is given by its equations, and the Lean relation reads them the way kompile emits them. Under σ, rule 1's right-hand side is a term to evaluate: `EvalTerm c σ t v` says that `t` has the value `v`." },
        { hl: { e: span(evaluation, '| ctor {σ : Subst} {f : String}', 'EvalTerm c σ (.app f ts) (.ctor f vs)') }, notes: [note('e', lineOf(evaluation, '| ctor {σ : Subst} {f : String}'), "A head that is a constructor of peano builds the constructor term.")] },
        { hl: { e: [lineOf(evaluation, '| var {σ : Subst} {i : Nat}')] }, notes: [note('e', lineOf(evaluation, '| var {σ : Subst} {i : Nat}'), "A variable is its value in σ: X2 is the counter cell, X1 is `s(z)`.")] },
        { hl: { e: span(evaluation, '| call {σ : Subst}', '(hf : Eval c f vs v) : EvalTerm c σ (.app f ts) v') }, notes: [note('e', lineOf(evaluation, '| call {σ : Subst}'), "`pred` is no constructor, so `pred(X1)` is a function call, whose value is given by `Eval`.")] },
        { hl: { e: span(evaluation, '| clause {f : String}', '(hrhs : EvalTerm c σ cl.rhs v) : Eval c f vs v') }, notes: [note('e', lineOf(evaluation, '| clause {f : String}'), "The first clause whose patterns match the arguments decides.")], say: "Clause 0, `pred(s(X0))`, matches `s(z)` with X0 ↦ z." },
        { hl: { e: [lineOf(evaluation, '(hrhs : EvalTerm c σ cl.rhs v) : Eval c f vs v')] }, notes: [note('e', lineOf(evaluation, '(hrhs : EvalTerm c σ cl.rhs v) : Eval c f vs v'), "X0 has the value `z` under that σ, so `pred(s(z))` has the value `z`.")] },
        {
          hl: { e: [lineOf(evaluation, "(hpre : ∀ cl' ∈ pre, matchTerms c cl'.pats vs = none)"), lineOf(evaluation, '(hmatch : matchTerms c cl.pats vs = some σ)')] },
          notes: [note('e', lineOf(evaluation, "(hpre : ∀ cl' ∈ pre, matchTerms c cl'.pats vs = none)"), "No clause before the deciding one may match.", 'hpre')],
          ask: {
            q: "If the deciding clause's right-hand side had no value, could a later clause give one?",
            options: ["Yes, evaluation falls through to the next clause", "No: the clause that matches decides, so the function has no value at those arguments", "Only the `[owise]` clause could"],
            answer: 1,
            why: "The KORE equations' premises read the arguments only. Nothing else gets a say.",
          },
        },
        { hl: { e: span(evaluation, '| owise {f : String}', '(hrhs : EvalTerm c (argSubst 0 vs) o.rhs v) : Eval c f vs v') }, notes: [note('e', lineOf(evaluation, '| owise {f : String}'), "Applies exactly where no clause matches.")], say: "Lean computes `pred(z)` as `z` by the catch-all clause. Nothing else gives a value." },
        { hl: { e: span(evaluation, '| inj {σ : Subst} {a b : String}', 'EvalTerm c σ (.inj a b t) (injNormal a b v)') }, say: "The injection is kept in normal form, and the whole right-hand side has the value `" + kc(c1.term) + "` in the k cell: the configuration `c1`." },
      ],
    },
    {
      id: 's8',
      title: 'run(s(z)) → run(z) → done(z)',
      visual: stepChain,
      arrange: 'top',
      panes: [{ id: 's', label: 'One rewrite step', source: step }],
      frames: [
        { hl: { s: span(step, 'inductive Step (c : Semantics)', '(heval : EvalTerm c σ r.rhs y.val) : Step c x y') }, notes: [note('s', lineOf(step, 'inductive Step (c : Semantics)'), "One constructor: a rule of the definition, the σ its match gives, and the value of its right-hand side under σ.")], say: "That's all a step is." },
        { hl: { s: [lineOf(step, '(hmatch : matchTerm c r.lhs x.val = some σ)'), lineOf(step, '(heval : EvalTerm c σ r.rhs y.val)')] }, notes: [note('s', lineOf(step, '(hmatch : matchTerm c r.lhs x.val = some σ)'), "`runSucc` matches `c0`, with σ.", 'hmatch'), note('s', lineOf(step, '(heval : EvalTerm c σ r.rhs y.val)'), "Its right-hand side has the value `c1`.", 'heval')], say: "So `Step c0 c1`." },
        { hl: { s: [lineOf(step, '| rule {x y : Config c} (r : Rule) (mem : r ∈ c.rules)')] }, say: "`runZero` does not match `c0`, so `c0` has one successor. The executable step lists exactly `[c1]`." },
        { hl: { s: [lineOf(step, '(hmatch : matchTerm c r.lhs x.val = some σ)'), lineOf(step, '(heval : EvalTerm c σ r.rhs y.val)')] }, say: "From `c1`, `runZero` matches with `" + substText(zero1.match ?? []) + "` and writes `" + kc(c2.term) + "`: `Step c1 c2`." },
        {
          hl: { s: [lineOf(step, '| rule {x y : Config c} (r : Rule) (mem : r ∈ c.rules)')] },
          say: "From `c2` neither rule matches, and the executable step lists no successor. `done(z)` is stuck, which is how this run ends.",
          ask: {
            q: "The equations of `pred` apply inside terms. Does `Step` apply a rule inside a term too?",
            options: ["Yes, at any position", "No, and it need not: kompile has already made each rule a rule on the whole configuration", "Only inside the k cell"],
            answer: 1,
            why: "With the other cells as variables, a step at the top is K's step. These definitions have no `requires`, `ensures` or priorities: no field of a rule holds them.",
          },
        },
        { hl: { s: [lineOf(step, 'inductive Step (c : Semantics) : Config c → Config c → Prop where')] }, notes: [note('s', lineOf(step, 'inductive Step (c : Semantics) : Config c → Config c → Prop where'), "Both ends range over `Config c`: a right-hand side whose value is not of the configuration sort gives no step.", 'Config c → Config c')] },
      ],
    },
    {
      id: 's9',
      title: 'Where the fuel went',
      panes: [
        { id: 'e', label: 'The frozen relation', source: evaluation },
        { id: 'f', label: 'The executable evaluator (checked layer)', source: fuel },
      ],
      frames: [
        { hl: { e: span(evaluation, 'There is no fuel and no termination argument', 'relation for the definitions it accepts') }, notes: [note('e', lineOf(evaluation, 'There is no fuel and no termination argument'), "`Eval` is a relation, and `Step` reads it.")], say: "An evaluator that runs needs a bound on its recursion. A relation does not, so its meaning contains ==no bound to review==." },
        {
          hl: { f: span(fuel, 'def evalWithFuel', '| n + 1, vs =>') },
          notes: [note('f', lineOf(fuel, 'def evalWithFuel'), "Each self call gets one unit less, and at zero the value is `none`.")], say: "To compute a step, `Execution.lean` has `evalWithFuel`.",
          ask: {
            q: "Why not define the step with the fueled evaluator directly?",
            options: ["It would be too slow", "What a step means would depend on a fuel bound, an arbitrary cutoff inside the meaning of every statement", "Lean cannot compute with fuel"],
            answer: 1,
            why: "With the relation, that the fuel always suffices is a theorem, proved once (`Eval.complete`), not a choice a reader has to review.",
          },
        },
      ],
    },
    {
      id: 's10',
      title: 'Why the evaluator has fuel at all',
      panes: [
        { id: 'f', label: 'The executable evaluator', source: fuel },
        { id: 'n', label: 'Its fuel', source: fnFuel },
      ],
      frames: [
        { hl: { n: span(fnFuel, 'def Fn.fuel', '| none => 0) + 1') }, notes: [note('n', lineOf(fnFuel, 'def Fn.fuel'), "One more than the size of the argument at the position where every self call shrinks.")], say: "A call starts with `Fn.fuel`." },
        { hl: { f: [lineOf(fuel, '| 0, _ => none')] }, say: "Lean's kernel does not reduce well-founded recursion, so explicit fuel is what lets the kernel run the evaluator on closed terms." },
      ],
    },
    {
      id: 's11',
      title: 'What ties them together',
      panes: [
        { id: 'i', label: 'What ties them', source: iff },
        { id: 'r', label: 'The condition', source: ready },
      ],
      frames: [
        { hl: { i: [lineOf(iff, 'theorem step_iff (hr : c.evalReady = true)'), lineOf(iff, 'theorem eval_iff (hr : c.evalReady = true)')] }, notes: [note('i', lineOf(iff, 'theorem step_iff (hr : c.evalReady = true)'), "`Step c x y ↔ y ∈ successors c x`, proved once, for every definition that `evalReady` accepts.")] },
        {
          hl: { r: span(ready, 'def Semantics.evalReady', 'nodup (c.fns.map') },
          notes: [note('r', lineOf(ready, 'def Semantics.evalReady'), "A check on the data: distinct labels, fuel that suffices, no call of a later function.")],
          ask: {
            q: "If `evalWithFuel` had a bug, could a wrong statement about `Step` be proved?",
            options: ["Yes, every proof runs through it", "No: statements mention `Step`, not `successors`, and a wrong evaluator would make `step_iff` unprovable", "Only for peano"],
            answer: 1,
            why: "A proof that used a broken `step_iff` would not check.",
          },
        },
      ],
    },
    {
      id: 's12',
      title: 'Two descriptions of a step',
      panes: [
        { id: 'p', label: 'On peano', source: checks },
        { id: 'w', label: 'Under wf alone', source: iffWf },
      ],
      frames: [
        { hl: { p: [lineOf(checks, 'theorem evalReady_peano'), lineOf(checks, 'theorem step_iff_peano')] }, notes: [note('p', lineOf(checks, 'theorem evalReady_peano'), "For peano the kernel decides it."), note('p', lineOf(checks, 'theorem step_iff_peano'), "So peano's executable step is its frozen step.")] },
        { hl: { w: span(iffWf, 'theorem step_iff_wf', 'step_iff (wf_evalReady') }, notes: [note('w', lineOf(iffWf, 'theorem step_iff_wf'), "The same for any definition that is well formed, with no further check.")] },
        { say: "So there are two descriptions of a step. ==`Step`== is what statements are about. ==`successors`== is what the kernel can compute on closed terms, and lesson 5 uses its one-rule form, `stepAt`, to prove facts about particular configurations. `step_iff` makes either usable in a proof about the other." },
      ],
    },
  ],
  quiz: [
    {
      q: "Why does `inj{Val,KItem}(inj{Nat,Val}(z))` have no sort, while `inj{Nat,KItem}(z)` has one?",
      options: ["`Val` is not below `KItem`", "The two denote the same element in every model, so only one may represent it: `sortOf` rejects an injection directly on another", "`z` is not a `Nat`"],
      answer: 1,
      why: "Every sort below `KItem` has its own pair `(X, KItem)` in the subsort list, so the second form exists for every such sort.",
    },
    {
      q: "A pattern `inj{Val,KItem}(V)` meets the term `inj{Nat,KItem}(z)`. Does it match?",
      options: ["No, the sorts differ", "Yes, because `Nat < Val`: V is bound to `inj{Nat,Val}(z)`, which denotes the same element", "Yes, and V is bound to `z`"],
      answer: 1,
      why: "That's K's subsort semantics: a pattern of sort `Val` matches every term of a sort below `Val`. peano's two rules never need it.",
    },
    {
      q: "What value does `Eval` give `pred(\\dv{Int}(\"5\"))`?",
      options: ["No value, it is ill-sorted", "`z`, by the catch-all clause: the pattern `s(X0)` does not match a domain value", "`4`"],
      answer: 1,
      why: "Lean computes the same. `Eval` is defined on every ground term, not only on terms of sort `Nat`, so the equations of `pred` hold more widely than K's.",
    },
    {
      q: "Can `Eval` run forever on a function that never terminates?",
      options: ["Yes, so it needs fuel", "It does not run at all: it is an inductive relation, so a value exists only with a finite derivation", "No, Lean rejects such functions"],
      answer: 1,
      why: "A function that does not terminate at some arguments has no value there.",
    },
    {
      q: "Where does the counter cell come from, if `peano.k` never mentions it?",
      options: ["From krust's runtime", "From the configuration kompile generates: it turns each rule into one on that whole configuration, and the cells a rule does not mention become variables", "From `peanoCore`'s author"],
      answer: 1,
      why: "That's the variable `.var 2` in both rules.",
    },
    {
      q: "Which configuration does `Step` relate to nothing, and what relies on it?",
      options: ["`c0`, and determinism", "`c2`, with `done(z)` in the k cell; the witness `stuck_done` in lesson 5 proves it", "None: every configuration steps"],
      answer: 1,
      why: "It shows that `Step` does not relate every configuration to something.",
    },
  ],
  checked: [
    "`step_iff`, `eval_iff` and `Eval.complete` (fuel always suffices) are kernel-checked theorems for every definition that passes `evalReady`; `step_iff_wf` needs only that the definition is well formed.",
    "`evalReady_peano` is a kernel decision on peano's data.",
    "The substitutions, values and successors shown were computed by Lean on `peanoCore` with the executable evaluator, which these theorems tie to the relation. For `run(s(z)) → run(z)`, `run(z) → done(z)` and the stuck `done(z)`, lesson 5 proves the same facts about `Step` itself.",
    "Subject reduction, proved since this lesson was first written: in a well-formed definition, a function at arguments of its argument sorts returns a value of its result sort (`Eval.sorted_wf`), and a rule whose left-hand side matches a configuration rewrites it to a configuration (`rhs_sorted_wf`), so no rule application is lost to the sort filter of `successors` (`step_of_match_wf`).",
  ],
  tryit: [
    { say: "In the kcore-spec package directory (Lean 4.34.0, no Mathlib):", cmd: "lake build        # the library, its checks and the proofs" },
    {
      say: "Then put this in a file in the package and run `lake env lean FILE`:",
      cmd: "import KcoreSpec\nopen KCore KCore.Peano.Ground\n\n-- the substitution of rule runSucc on run(s(z))\n#eval matchTerm Peano.peanoCore runSucc.lhs (cfg (run (s z)) ctr0)\n-- the value of pred(s(z)) by the executable evaluator\n#eval eval Peano.peanoCore \"Lblpred\" [s z]\n-- the successors of run(s(z)), run(z) and done(z)\n#eval [cfg (run (s z)) ctr0, cfg (run z) ctr0, cfg (done (natVal z)) ctr0].map fun t =>\n  (Value.ofTerm Peano.peanoCore topCellSort t).map fun x => (successors Peano.peanoCore x).map (·.val)",
    },
    { say: "The first line prints `some [(0, z), (1, s(z)), (2, <generatedCounter>(0))]` in Lean's notation for the data, and the last prints one successor, one successor and none." },
  ],
}
