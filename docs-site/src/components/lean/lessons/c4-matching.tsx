'use client'

// Core lesson 4: matching. `PatVal c σ p v`, the relation saying the pattern p denotes the value v
// under σ, including map and list patterns; and well-sorted substitutions. Every Lean pane is
// kcore-spec's text at the manifest's commit, as are kimp's KORE axiom and colls-list.k; the
// matches shown are worked by hand from those definitions.

import { type Source, coreCommit, coreFile, lineOf, slice, span, textSource } from '../data'
import { type Lesson, note } from '../lesson'

const ev = coreFile('KcoreSpec/Evaluation.lean')
const patVal = slice(ev, '  /-- `PatVal c σ p v`:', '        (h : PatVal c σ p v) (hs : PatVals c σ ps vs) : PatVals')
const wellSorted = slice(ev, '/-- σ gives each variable of the list', 'c.sortOf v = some s')
const kimpVar = coreFile('examples/kimp/Kimp/definition.kore#CALC.var')
const colls = coreFile('f2-examples/colls-list.k')

const workedRun = textSource('worked by hand', [
  "-- the k cell of peano's first rule, run(s(N) #as V), against run(s(s(z)))",
  '-- (names for numbers, as in lesson 1)',
  'σ = [(0, s(z)), (1, s(s(z)))]                    -- N is s(z), V is s(s(z))',
  'PatVal c σ (.var 0) s(z)                          -- var: σ gives 0 the value s(z)',
  'PatVal c σ (.app s [.var 0]) s(s(z))              -- ctor: s is a constructor',
  'PatVal c σ (.as (.app s [.var 0]) 1) s(s(z))      -- as: and σ gives 1 the same value',
  'PatVal c σ (.app run [.as (.app s [.var 0]) 1]) run(s(s(z)))   -- ctor',
].join('\n'))
const workedMap = textSource('worked by hand', [
  '-- the env cell holds {x ↦ 1, y ↦ 2}',
  '-- its pattern: _Map_(X |-> V, M)',
  '',
  'σ₁ = [X ↦ x, V ↦ 1, M ↦ {y ↦ 2}]     -- {x ↦ 1} joined with {y ↦ 2}',
  'σ₂ = [X ↦ y, V ↦ 2, M ↦ {x ↦ 1}]     -- {y ↦ 2} joined with {x ↦ 1}',
  '',
  '-- the k cell holds x, and X there too:',
  '-- only σ₁ matches the whole left side',
].join('\n'))

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)
const envFirst = at(kimpVar, "Lbl'-LT-'env'-GT-'")
const envMap = span(kimpVar, "Lbl'Unds'Map'Unds'{}(", "Var'Unds'DotVar2:SortMap{}")

export const matching4: Lesson = {
  id: 'matching',
  number: 4,
  title: 'Matching',
  against: coreCommit,
  scenes: [
    {
      id: 'm1',
      title: 'Matching is a relation',
      panes: [
        { id: 'p', label: 'KcoreSpec/Evaluation.lean', source: patVal, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedRun, lang: 'lean' },
      ],
      frames: [
        {
          hl: { p: [at(patVal, 'inductive PatVal')] },
          notes: [note('p', at(patVal, 'inductive PatVal'), 'The pattern `p` denotes the value `v` under σ.', 'Term → GroundTerm → Prop')],
          say: 'Matching is not a program here. `PatVal` says when a match holds, so a pattern and a value may have several substitutions, or none.',
        },
        {
          hl: { p: [at(patVal, '| var {i : Nat}'), ...span(patVal, '| ctor {f : Sym}', '(h : c.isCtor f = true)')], w: [at(workedRun, 'σ = ['), at(workedRun, 'PatVal c σ (.var 0)'), at(workedRun, 'PatVal c σ (.app s'), at(workedRun, 'PatVal c σ (.app run')] },
          notes: [
            note('p', at(patVal, '| var {i : Nat}'), 'A variable denotes the value σ gives it.', 'σ.lookup i = some v'),
            note('p', at(patVal, '(h : c.isCtor f = true)'), "A constructor denotes the constructor term of its arguments' values.", 'c.isCtor f = true'),
          ],
        },
        {
          hl: { p: [at(patVal, '| dv {s : Srt}')] },
          notes: [note('p', at(patVal, '| dv {s : Srt}'), 'A literal denotes itself.', '(.dv s lit) (.dv s lit)')],
        },
      ],
    },
    {
      id: 'm2',
      title: 'Injections and aliases',
      panes: [
        { id: 'p', label: 'KcoreSpec/Evaluation.lean', source: patVal, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedRun, lang: 'lean' },
      ],
      frames: [
        {
          hl: { p: span(patVal, '| inj {a b : Srt}', 'PatVal c σ (.inj a b p) (injNormal a b w)') },
          notes: [note('p', at(patVal, 'PatVal c σ (.inj a b p) (injNormal a b w)'), "An injection denotes its pattern's value, injected. If that value is already an injection, the two become one, so the value is never an injection of an injection.", 'injNormal')],
        },
        {
          hl: { p: span(patVal, '| as {p : Term}', 'PatVal c σ (.as p i) v'), w: [at(workedRun, 'σ = ['), at(workedRun, 'PatVal c σ (.as')] },
          notes: [note('p', at(patVal, '| as {p : Term}'), 'An alias denotes what its pattern denotes, and σ gives its variable that same value.', 'σ.lookup i = some v')],
        },
      ],
    },
    {
      id: 'm3',
      title: 'A map in a rule',
      panes: [
        { id: 'k', label: 'Kimp/definition.kore', source: kimpVar, lang: 'kore' },
        { id: 'w', label: 'Worked by hand', source: workedMap, lang: 'lean' },
      ],
      frames: [
        {
          hl: { k: [envFirst, ...envMap] },
          notes: [note('k', envMap[0], "kimp looks up a variable: the env cell's map is `X |-> V` joined with the rest, `M`.", "Lbl'Unds'Map'Unds'")],
          say: "kimp is a small imperative language. This rule replaces a variable `X` in the k cell by its value `V` in the env cell.",
        },
        {
          hl: { w: span(workedMap, 'σ₁ =', 'σ₂ =') },
          notes: [note('w', at(workedMap, 'σ₂ ='), 'A map has no first entry: both ways to split it match.', 'σ₂')],
        },
        {
          hl: { k: [at(kimpVar, 'kseq{}(inj{SortId{}, SortKItem{}}(VarX:SortId{})')], w: span(workedMap, '-- the k cell holds x', '-- only σ₁') },
          notes: [note('k', at(kimpVar, 'kseq{}(inj{SortId{}, SortKItem{}}(VarX:SortId{})'), 'The same `X`, in the k cell.', 'VarX')],
        },
      ],
    },
    {
      id: 'm4',
      title: 'Map patterns denote maps',
      panes: [
        { id: 'p', label: 'KcoreSpec/Evaluation.lean', source: patVal, lang: 'lean' },
        { id: 'w', label: 'Worked by hand', source: workedMap, lang: 'lean' },
      ],
      frames: [
        {
          hl: { p: span(patVal, '| hook {f : Sym}', '(hv : hook f vs = some (some v))'), w: span(workedMap, 'σ₁ =', 'σ₂ =') },
          notes: [note('p', at(patVal, '| hook {f : Sym}'), '`.Map`, `|->` and `_Map_` denote the map they build. `K |-> V M` is defined only when `K` is not already a key of `M`.', 'hook')],
          say: 'So a map pattern matches exactly the ways of splitting the map, with no order between entries.',
        },
      ],
    },
    {
      id: 'm5',
      title: 'List patterns',
      panes: [
        { id: 'k', label: 'colls-list.k', source: colls, lang: 'k' },
        { id: 'p', label: 'KcoreSpec/Evaluation.lean', source: patVal, lang: 'lean' },
      ],
      frames: [
        {
          hl: { k: [at(colls, 'configuration'), at(colls, 'rule <k> pop')] },
          notes: [note('k', at(colls, 'configuration'), 'The stack starts as the list `[1, 2]`.', 'ListItem(1) ListItem(2)'), note('k', at(colls, 'rule <k> pop'), 'Matches with `X` = 1 and `L` = `[2]`.', 'ListItem(X:Int) L:List')],
        },
        {
          hl: { k: [at(colls, 'rule <k> drop')] },
          notes: [note('k', at(colls, 'rule <k> drop'), 'From the back: `L` = `[1]`.', 'L:List ListItem(_)')],
        },
        {
          hl: { p: span(patVal, '| coll {f : Sym}', 'PatVal c σ (.app f ps) v', at(patVal, '| coll {f : Sym}') - 1) },
          notes: [note('p', at(patVal, '| coll {f : Sym}'), 'A list symbol denotes the list it builds from the values of its parts.', 'coll')],
        },
      ],
    },
    {
      id: 'm6',
      title: 'Well-sorted substitutions',
      panes: [{ id: 'e', label: 'KcoreSpec/Evaluation.lean', source: wellSorted, lang: 'lean' }],
      frames: [
        {
          hl: { e: span(wellSorted, 'def WellSorted', 'c.sortOf v = some s') },
          notes: [note('e', at(wellSorted, 'def WellSorted'), 'Every variable of the list gets a value of its sort.', 'WellSorted')],
          say: "A clause and a rule list their variables' sorts (lesson 2). Lessons 5 and 6 ask every match to be well sorted for that list.",
        },
      ],
    },
  ],
  quiz: [
    {
      q: 'kimp\'s env cell holds `{x ↦ 1, y ↦ 2}`. How many substitutions make `X |-> V M` denote it, before the k cell is considered?',
      options: ['Two: one per entry', 'One: the first entry', 'None: maps cannot be matched'],
      answer: 0,
      why: 'A map has no order, so each entry can be the `X |-> V`, with the rest as `M`.',
    },
    {
      q: 'What does `PatVal c σ p v` say?',
      options: ['Under σ, the pattern p denotes the value v', 'Matching p against v returns σ', 'p and v have the same sort'],
      answer: 0,
      why: 'It is a relation. Lesson 6 asks for some σ with the left side denoting the configuration.',
    },
  ],
  checked: [
    `The Lean in every pane is kcore-spec's text at \`${coreCommit}\`, and so are kimp's KORE axiom and \`colls-list.k\`.`,
    'The substitutions shown are worked by hand from `PatVal`. Lean did not compute them.',
  ],
}
