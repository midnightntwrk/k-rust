'use client'

// Lesson 9: the fragment that adds several cells, Bool and Int, `requires` and maps, on the store
// example. The configurations, matches and successors were computed by Lean with F1's executable
// step (FactsF1.lean), which `step_iff` proves equal to F1's `Step` for every well-formed
// definition; the panes are F1's source at the recorded commit.

import { configF1, type F1Binding, lean, lineOf, source, span, textSource } from '../data'
import { type Lesson, note } from '../lesson'
import { f1Numbers } from '../numbers'
import { Bar, Rows } from '../viz'

const storeK = textSource('store.k', lean.storeK)
const storeCore = source('f1StoreCore')
const f1Step = source('f1Step')
const patVal = source('f1PatVal')
const groundTerm = source('f1GroundTerm')
const keysSorted = source('f1KeysSorted')
const matcher = source('f1Matcher')
const stepIff = source('f1StepIff')
const stepOfF0 = source('f1StepOfF0')
const stepOfF0False = source('f1StepOfF0False')
const hookWitness = source('f1HookWitness')
const hookWitnessStep = source('f1HookWitnessStep')
const hooksApart = source('f1HooksApart')

const mp = lean.factsF1.mapPattern
const get2 = configF1('get2')
const get7 = configF1('get7')
const put0 = configF1('put')
const getMatches = get2.rules.find((r) => r.rule === 'get')?.matches
if (mp.free.length !== 3 || mp.keyBound.length !== 1 || mp.keyAbsent.length !== 0 || getMatches?.length !== 1 || get2.successors.length !== 1 || get7.successors.length !== 0 || put0.successors.length !== 1) {
  throw new Error('lean lessons: the computed map matches are not the ones lesson 9 describes')
}

const names = ['K', 'V', 'M']
const bindingText = (b: F1Binding[]) => b.filter((x) => x.var < names.length).map((x) => `${names[x.var]} = ${x.value}`).join(', ')
const keyBoundValue = mp.keyBound[0].find((x) => x.var === 1)?.value

/** The k and state cells of a store configuration as Lean rendered it: the cells the rules change. */
function cellsText(conf: string): string {
  const k = conf.match(/<k> .*? <\/k>/)?.[0]
  const st = conf.match(/<state> .*? <\/state>/)?.[0]
  if (!k || !st) throw new Error(`lean lessons: ${conf} has no k or state cell`)
  return `${k} ${st}`
}
const cell = (conf: string, name: 'k' | 'state') => conf.match(new RegExp(`<${name}> (.*?) </${name}>`))?.[1]
const get2Next = cell(get2.successors[0], 'k')
const put0State = cell(put0.successors[0], 'state')

const matchRows = [
  { label: 'nothing bound', matches: mp.free },
  { label: `K = ${mp.keyBound[0].find((x) => x.var === 0)?.value}, from the k cell`, matches: mp.keyBound },
  { label: 'K = 7, from the k cell', matches: mp.keyAbsent },
]

const matchTable = (lit: readonly (number | null)[]) => (at: number) => (
  <Rows
    head={[`${mp.pattern} against ${mp.map}`, 'matches, computed']}
    rows={matchRows.map((r, i) => ({
      key: r.label,
      state: lit[at] === null ? undefined : lit[at] === i ? ('cur' as const) : ('faded' as const),
      cells: [
        <span key="l" style={{ fontFamily: 'var(--f-sans)' }}>{r.label}</span>,
        r.matches.length === 0 ? <span key="n" style={{ fontFamily: 'var(--f-sans)' }}>none</span> : <span key="m">{r.matches.map((m) => <div key={bindingText(m)}>{bindingText(m)}</div>)}</span>,
      ],
    }))}
  />
)

const successorTable = (at: number) => (
  <Rows
    head={['configuration (its k and state cells)', 'successors, computed']}
    rows={[get2, get7, put0].map((c, i) => ({
      key: c.name,
      state: at === i ? ('cur' as const) : ('faded' as const),
      cells: [
        cellsText(c.text),
        c.successors.length === 0 ? <span key="n" style={{ fontFamily: 'var(--f-sans)' }}>none (stuck)</span> : <span key="s">{c.successors.map((s) => <div key={s}>{cellsText(s)}</div>)}</span>,
      ],
    }))}
  />
)

const differential = (at: number) => (
  <Rows
    head={['F₁ execution differential', { text: '', num: true }]}
    rows={[
      { key: 'defs', cells: ['definitions', f1Numbers.subjects] },
      { key: 'configs', cells: ['configurations compared with krust', f1Numbers.configs] },
      { key: 'diff', state: at === 2 ? ('cur' as const) : undefined, cells: ['differences and errors', f1Numbers.differences] },
      { key: 'ref', state: at === 2 ? ('cur' as const) : undefined, cells: ['agreeing with the reference, of those sampled', `${f1Numbers.refAgree} / ${f1Numbers.refSampled}`] },
      { key: 'cap', cells: ['left unexplored at the size cap', f1Numbers.unexplored] },
    ].map((r) => ({ ...r, cells: [<span key="w" style={{ fontFamily: 'var(--f-sans)' }}>{r.cells[0]}</span>, r.cells[1]] }))}
  />
)

const coneMax = lean.f1Cones.root.totals.total.coneLines
const cones = (at: number) => (
  <Rows
    head={['what you read', { text: 'lines', num: true }, { text: '', bar: true }]}
    rows={[
      { key: 'f0', state: at === 0 ? ('cur' as const) : undefined, cells: ["peano's statements, over F₀", f1Numbers.f0User, <Bar key="b" pct={(f1Numbers.f0User / coneMax) * 100} />] },
      { key: 'f1', state: at === 0 ? ('cur' as const) : undefined, cells: ["peano's statements, over F₁", f1Numbers.user, <Bar key="b" pct={(f1Numbers.user / coneMax) * 100} />] },
      { key: 'emit', state: at === 2 ? ('cur' as const) : undefined, cells: ["F₁'s generator", f1Numbers.emit, <Bar key="b" pct={(lean.f1Cones.emit.totals.total.coneLines / coneMax) * 100} />] },
      { key: 'root', state: at === 2 ? ('cur' as const) : undefined, cells: ["F₁'s matching-logic track", f1Numbers.root, <Bar key="b" pct={100} />] },
    ].map((r) => ({ ...r, cells: [<span key="w" style={{ fontFamily: 'var(--f-sans)' }}>{r.cells[0]}</span>, r.cells[1], r.cells[2]] }))}
  />
)

export const lesson9: Lesson = {
  id: 'beyond-peano',
  number: 9,
  title: 'Beyond peano: the builtin fragment',
  scenes: [
    {
      id: 'f1',
      title: "A definition peano's fragment cannot hold",
      panes: [{ id: 'k', label: 'store.k', source: storeK, lang: 'k' }],
      frames: [
        { say: "Lessons 3 to 8 are about the constructor fragment, F₀, and peano fits it, but almost nothing else does: it has one cell, no numbers, no side conditions and no collections. Real definitions have all four. The ==builtin fragment==, F₁, adds all four, and this small definition uses three of them. Its Int, Bool and Map operations are ==hooks==: K's `hook` attribute says the backend supplies the operation, and kompile writes no equations defining it." },
        { hl: { k: [lineOf(storeK, 'configuration')] }, notes: [note('k', lineOf(storeK, 'configuration'), "Two cells inside `<T>`: the program in `<k>`, and a map in `<state>`.")] },
        { hl: { k: [lineOf(storeK, 'rule [put]')] }, notes: [note('k', lineOf(storeK, 'rule [put]'), "`put` writes a key."), note('k', lineOf(storeK, 'rule [put]'), "the map `M` with `K` set to `V`", 'M [ K <- V ]')] },
        { hl: { k: [lineOf(storeK, 'rule [get]')] }, notes: [note('k', lineOf(storeK, 'rule [get]'), "`get` reads one."), note('k', lineOf(storeK, 'rule [get]'), "some entry with key `K`, whatever the rest; it's the same `K` as in the k cell", 'K |-> V _')] },
        {
          hl: { k: [lineOf(storeK, 'rule [new]')] },
          notes: [note('k', lineOf(storeK, 'rule [new]'), "a fresh integer", '!I:Int')],
          say: "kompile compiles `!I:Int` into a counter cell: the rule reads the counter, uses it, and writes it plus one.",
          ask: {
            q: "Where does `!I:Int` go in the core kompile writes?",
            options: ["It stays a special kind of variable the step has to know about", "Into the `<generatedCounter>` cell: to the step it's Int arithmetic on an ordinary cell", "It's dropped, since no later rule reads it"],
            answer: 1,
            why: "`new` reads the counter, uses `freshInt` of it, and writes it plus one.",
          },
        },
      ],
    },
    {
      id: 'f2',
      title: 'The same definition, as F₁ data',
      panes: [
        { id: 'k', label: 'store.k', source: storeK, lang: 'k' },
        { id: 'c', label: 'Its core, as F₁ data', source: storeCore },
      ],
      frames: [
        {
          hl: { c: span(storeCore, 'def storeCore : Semantics', 'config := .node "T"') },
          notes: [note('c', lineOf(storeCore, 'def storeCore : Semantics'), "The constructors, the configuration's cell tree and the three rules, as kompile wrote them, counter cell included.")],
        },
        {
          hl: { c: span(storeCore, '-- get: K V Gen0 Gen6 DotVar0', '(.var 4), none,'), k: [lineOf(storeK, 'rule [get]')] },
          notes: [
            note('c', lineOf(storeCore, '(.as (.app'), "the whole state cell gets a name too: an as-pattern", '.as'),
            note('c', lineOf(storeCore, '(.as (.app'), "`_Map_` of one `|->` element and a frame variable", 'mapConcat'),
          ],
        },
      ],
    },
    {
      id: 'f3',
      title: 'A map has one form',
      panes: [
        { id: 'g', label: 'Values', source: groundTerm },
        { id: 's', label: 'Canonical maps', source: keysSorted },
      ],
      frames: [
        {
          hl: { g: span(groundTerm, '/-- a finite map', '| map (es'), s: span(keysSorted, 'def keysSorted', '| _ => true') },
          notes: [note('s', lineOf(keysSorted, 'def keysSorted'), "Each key is strictly below the next, so no key appears twice.")],
          say: "A map value is a list of entries sorted by key. So each map has ==exactly one representation==, and two maps are equal exactly when their lists are.",
        },
      ],
    },
    {
      id: 'f4',
      title: 'What a match is',
      visual: matchTable([null, 0]),
      arrange: 'top',
      panes: [{ id: 'p', label: 'What a match is (frozen)', source: patVal }],
      frames: [
        {
          hl: { p: span(patVal, '/-- `PatVal c σ p v`', 'σ under which the pattern denotes the map.') },
          say: "When does `K |-> V M` match a map? F₁ gives no algorithm. The pattern matches when it ==denotes== the map: the one-entry map K ↦ V, joined with M, is the map. The join is defined only when K is not already a key of M.",
        },
        {
          hl: { p: [lineOf(patVal, '| hook {f : String}')] },
          notes: [note('p', lineOf(patVal, '| hook {f : String}'), "The map symbols denote their values, through the same hook that computes them.", 'hook')],
          say: "Take " + mp.map + ", with nothing bound yet. " + mp.free.length + " substitutions make the pattern denote it, one per entry. Lean's matcher lists exactly these.",
          ask: {
            q: "Why define a match as \"the pattern denotes the value\" instead of giving the algorithm?",
            options: ["Algorithms can't be written in Lean", "With maps a pattern can match in several ways and share variables between cells; an algorithm is long, and the denotation is a few lines a reader can check", "The denotation runs faster"],
            answer: 1,
            why: "The algorithm lives in the checked layer, and `step_iff` proves it finds exactly the denoted matches.",
          },
        },
      ],
    },
    {
      id: 'f5',
      title: 'How Lean finds them',
      visual: matchTable([0, 1, 2]),
      arrange: 'top',
      panes: [{ id: 'm', label: 'How Lean finds them (checked)', source: matcher }],
      frames: [
        {
          hl: { m: span(matcher, '/-- Choose an entry for each element', '| none => []') },
          notes: [note('m', lineOf(matcher, '(List.range es.length).flatMap'), "tries every entry", 'flatMap')],
          say: "Each match picks an entry for K ↦ V and leaves the others as M. The order of entries in the pattern doesn't matter: that's matching ==modulo associativity and commutativity==.",
        },
        { say: "In the `get` rule, K is already bound by the k cell. With `get(2)`, only the entry with key 2 fits: one match, V = " + keyBoundValue + "." },
        {
          say: "With `get(7)` there is no entry with key 7, and no match.",
          ask: {
            q: "How many matches would `K |-> V M` have against a map of a hundred entries, with K bound by another cell?",
            options: ["A hundred", "At most one, because keys are distinct", "It depends on the order of the entries"],
            answer: 1,
            why: "With nothing bound it would be a hundred, one per entry.",
          },
        },
      ],
    },
    {
      id: 'f6',
      title: 'On the whole configuration',
      visual: successorTable,
      frames: [
        { say: "`get(2)` has exactly one successor, computed by Lean: `" + get2Next + "` in the k cell, the state unchanged." },
        { say: "`get(7)` has none: the configuration is stuck. No rule matches it." },
        { say: "`put(0, 1)` inserts key 0, and the result is again sorted: " + put0State + ". Keeping maps canonical is part of what each map operation does." },
      ],
    },
    {
      id: 'f7',
      title: 'One relation',
      panes: [{ id: 's', label: 'The step of F₁ (frozen)', source: f1Step }],
      frames: [
        {
          hl: { s: span(f1Step, 'inductive Step (c : Semantics)', '(heval : EvalTerm c σ r.rhs (some y.val)) : Step c x y') },
          notes: [
            note('s', lineOf(f1Step, '(hσ : c.WellSorted'), "each variable gets a value of its sort", 'hσ'),
            note('s', lineOf(f1Step, '(hmatch : PatVal'), "the match is the denotation above", 'hmatch'),
            note('s', lineOf(f1Step, '(hreq :'), "a `requires` clause must evaluate to `true`", 'hreq'),
          ],
          say: "The frozen step of F₁ has the same shape as F₀'s, with three changes.",
        },
        {
          hl: { s: [lineOf(f1Step, '(hmatch : PatVal')] },
          say: "A relation like this says what the steps are. It doesn't compute them: nothing in it enumerates the matches of a map.",
        },
      ],
    },
    {
      id: 'f8',
      title: 'One program, proved equal',
      visual: differential,
      arrange: 'top',
      panes: [{ id: 'i', label: 'step_iff (checked)', source: stepIff }],
      frames: [
        {
          hl: { i: span(stepIff, '/-- The executable step lists exactly', 'step_iff_of d hwf') },
          notes: [note('i', lineOf(stepIff, 'Step d.sem x y ↔'), "the program that enumerated the matches, some fuel away", 'successorsN')],
          say: "`step_iff` says the executable step lists exactly the relation's successors, for every well-formed definition. It's proved, with no `sorry`.",
        },
        {
          hl: { i: span(stepIff, 'theorem step_iff', 'Step d.sem x y ↔') },
          say: "That buys two things. Every successor Lean computed in this lesson is a step of the frozen relation, and every step is among them: the computed tables are ==facts about `Step`==.",
        },
        {
          say: "And a comparison of the executable step with K's own backends is a comparison of `Step` with them. On " + f1Numbers.subjects + " definitions in F₁, " + f1Numbers.configs + " configurations gave the same successors as krust, with " + f1Numbers.differences + " differences, and a sample of " + f1Numbers.refSampled + " agreed with the reference backend.",
          ask: {
            q: "What would a difference in the F₁ differential have meant, given `step_iff`?",
            options: ["A bug in the matcher", "That the frozen `Step` and krust disagree: either the definition of a step or krust is wrong there", "Nothing, differences are expected"],
            answer: 1,
            why: "`step_iff` rules out the matcher as the cause.",
          },
        },
      ],
    },
    {
      id: 'f9',
      title: 'F₁ beside F₀',
      panes: [{ id: 'o', label: 'F₁ agrees with F₀', source: stepOfF0 }],
      frames: [
        {
          hl: { o: span(stepOfF0, 'theorem step_ofF0', 'KCore.Step d.sem x y ↔ Step (ofF0 d.sem)') },
          notes: [note('o', lineOf(stepOfF0, 'KCore.Step d.sem x y ↔ Step (ofF0 d.sem)'), "F₀'s step on the left, F₁'s on the right", '↔')],
          say: "F₁ sits beside F₀; it doesn't replace it. On an F₀ definition, F₁'s step is F₀'s, so everything proved for peano in F₀ carries over.",
        },
        {
          hl: { o: [lineOf(stepOfF0, 'theorem step_ofF0')] },
          notes: [note('o', lineOf(stepOfF0, 'theorem step_ofF0'), "F₀'s matching ignores sorts, and F₁'s substitutions are well sorted. This rules out a rule that binds a variable to a value of another sort.", 'hwf')],
        },
        {
          hl: { o: [lineOf(stepOfF0, '(hh : (ofF0 d.sem).hooksApart')] },
          notes: [note('o', lineOf(stepOfF0, '(hh : (ofF0 d.sem).hooksApart'), "This one has a story.", 'hooksApart')],
        },
      ],
    },
    {
      id: 'f10',
      title: 'A false conjecture',
      panes: [{ id: 'f', label: 'The refutation', source: stepOfF0False }],
      frames: [
        {
          hl: { f: span(stepOfF0False, '/-- `step_ofF0` is false as stated', 'KCore.Step d.sem x y ↔ Step (ofF0 d.sem)') },
          notes: [note('f', lineOf(stepOfF0False, 'theorem step_ofF0_false'), "No `hooksApart` in this statement, and a `¬` in front.")],
          say: "`step_ofF0` was first stated without its `hooksApart` hypothesis. Trying to prove it, the proof agent found it false, and proved that in Lean.",
        },
        { say: "The counterexample is peano with `pred` renamed to the KORE name of Int addition. F₀ knows no Int, so the name is just a function, evaluated by its clauses. F₁ reads that name as addition, applied to one argument, which is undefined." },
      ],
    },
    {
      id: 'f11',
      title: 'The gap it found',
      panes: [
        { id: 'w', label: 'The witness', source: hookWitness },
        { id: 'x', label: 'What the step did', source: hookWitnessStep },
      ],
      frames: [
        { say: "The real question was then about F₁ alone. F₁ decides that a symbol is a hook by its name. Could an F₁ definition name its own function like a hook?" },
        {
          hl: { w: span(hookWitness, 'def notCl : Clause', 'def notFn : Fn') },
          notes: [note('w', lineOf(hookWitness, 'def notFn : Fn'), "named like `notBool`", 'boolNot')],
          say: "Yes. This definition is peano plus a user function named like `notBool`, with the single clause `notBool(B) = B`, in a definition that doesn't import BOOL.",
        },
        {
          hl: { x: span(hookWitnessStep, '/-- `run(z)` in peano', 'Lblout') },
          say: "F₁'s well-formedness check accepted it. F₁'s step took `run(z)` to `out(false)`, by the hook. The KORE says `out(true)`, by the user's clause. ==The frozen step disagreed with the meaning of the text.==",
          ask: {
            q: "Why was this a soundness gap and not just an oddity?",
            options: ["It crashed the evaluator", "Soundness and completeness say the step lists exactly what the text's theory entails, and here it listed `out(false)` where the text entails `out(true)`, for a definition F₁ accepted", "It slowed the kernel down"],
            answer: 1,
            why: "Soundness and completeness would have been false for a definition in the fragment.",
          },
        },
      ],
    },
    {
      id: 'f12',
      title: 'The fix',
      panes: [{ id: 'a', label: 'The fix (reviewed layer)', source: hooksApart }],
      frames: [
        {
          hl: { a: span(hooksApart, '/-- No user constructor or function is named like a hooked symbol', 'd.sem.hooksApart') },
          notes: [note('a', lineOf(hooksApart, 'def Semantics.hooksApart'), "One condition in the reviewed layer. The witness is now rejected, by it alone.", 'hooksApart')],
        },
        {
          say: "No definition in the corpus was affected, and no differential could have found the gap, because no real definition does this. ==A conjecture, refuted in Lean, did.==",
        },
      ],
    },
    {
      id: 'f13',
      title: 'What changed in what you read',
      visual: cones,
      frames: [
        { say: "F₁'s frozen definitions are longer than F₀'s: the review cone of peano's statements, written over F₁, is " + f1Numbers.user + " lines against " + f1Numbers.f0User + " in F₀." },
        { say: "What grew: values (maps, literals in one form), the builtin operations' meanings (one table, `Hooks.lean`), matching as a denotation, and evaluation that can say \"undefined\", which `requires` needs." },
        { say: "The generator's cone is " + f1Numbers.emit + " lines and the matching-logic track's " + f1Numbers.root + "." },
      ],
    },
  ],
  quiz: [
    {
      q: "Which features of `store.k` are outside F₀?",
      options: ["Only the map", "The second cell, the Map, Int, and the map pattern in `get`", "`requires`"],
      answer: 1,
      why: "`requires` is in F₁ too, though this example doesn't use it.",
    },
    {
      q: "Why does `step_ofF0` need the hypothesis that F₀'s `wf` holds?",
      options: ["F₀'s matching ignores sorts and F₁'s substitutions are well sorted, so on a definition `wf` rejects, a rule could bind a variable in F₀ and not in F₁", "To make the proof shorter", "F₁ only accepts definitions F₀ rejects"],
      answer: 0,
      why: "The other hypothesis, `hooksApart`, has a story of its own.",
    },
    {
      q: "Why reject such names rather than read hooks from the definition's declarations?",
      options: ["Reading declarations would be unsound", "Both would work; the rejection is two short conditions a reader can check, costs nothing on the corpus, and keeps the hook table in one place", "Lean can't read declarations"],
      answer: 1,
      why: "It's a design choice, and the reviewed layer stays small.",
    },
  ],
  checked: [
    "Checked by the Lean kernel, with the axioms `propext`, `Classical.choice` and `Quot.sound` only: `step_iff`, for every definition F₁'s `wf` accepts, for some fuel.",
    "`step_ofF0`: on an F₀ definition that F₀'s `wf` accepts and that names nothing like a hook, F₁'s step is F₀'s. That the statement without the hook condition is false (`step_ofF0_false`), and that F₁ rejects the hook-named witness (`hookDef_not_wf`).",
    "That peano's KORE is in F₁ (`peano_F1`, from `parse`, `wf` and the comparison of the emitted KORE, each a kernel decision), and peano's nine properties restated over F₁. Subject reduction for F₁: a rule applied to a configuration of a well-formed definition gives a configuration.",
    "Computed, not proved: the tables of matches and successors, by Lean's compiled evaluation of the executable step. `step_iff` says what such a computation is worth, and the lesson checks the counts it describes. That the store example is in F₁ is a compiled check in the build.",
    "Evidence, not proof: the F₁ execution differential, " + f1Numbers.configs + " configurations of " + f1Numbers.subjects + " definitions, " + f1Numbers.differences + " differences against krust and " + f1Numbers.refAgree + " of " + f1Numbers.refSampled + " sampled configurations agreeing with the reference backend. " + f1Numbers.unexplored + " configurations were left unexplored at the size cap.",
    "Not proved: that F₁'s step is sound and complete, [lesson 8](/lean/sound-and-complete).",
  ],
  tryit: [
    { say: "In the kcore-spec package directory:", cmd: "lake build                        # F1's definitions, proofs and checks, with F0's\nlake env lean test/F1Check.lean   # peano in F1 and step_iff for peano, by the kernel; about 40 s" },
    {
      say: "Then put this in a file in the package and run `lake env lean FILE`:",
      cmd: "import KcoreSpec\nopen F1 F1.StoreExample F1.Exec\n\ndef three : Entries := [(gik 1, gik 5), (gik 2, gik 9), (gik 3, gik 4)]\n-- the matches of K |-> V M against {1 ↦ 5, 2 ↦ 9, 3 ↦ 4}, nothing bound\n#eval (matchP storeCore 20 [] (.app mapConcat [.app mapElem [ik (.var 0), ik (.var 1)], .var 2]) (.map three)).length\n-- the number of successors of get(2) and of get(7) on that state\n#eval [2, 7].map fun k => (successors storeCore (gcfg (.ctor \"Lblget\" [int k]) (gstate three) 0)).length",
    },
    { say: "They print `3` and `[1, 0]`." },
  ],
}
