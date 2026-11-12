'use client'

// Core lesson 3: values. Which ground terms are values of which sort (`sortOf`), and
// configurations as values of the top cell's sort. Every Lean pane is kcore-spec's text at the
// manifest's commit; the sorts shown are checked by Lean (docs-gen/lean_checks.py).

import { type Source, checked, checkedLabel, coreCommit, coreFile, lineOf, slice, span } from '../data'
import { type Lesson, note } from '../lesson'

const value = coreFile('KcoreSpec/Value.lean')
const sortOf = slice(value, '  /-- The sort of a ground term in `c`, or `none`', 'termination_by structural t => t')
const configDef = slice(value, 'def Value (c : Semantics)', 'abbrev Config')

const workedCtor = checked('sortCtor')
const workedInj = checked('sortInj')
const workedConfig = checked('sortConfig')

const at = (src: Source, needle: string, after = 0) => lineOf(src, needle, after)

export const values3: Lesson = {
  id: 'values',
  number: 3,
  title: 'Values',
  against: coreCommit,
  scenes: [
    {
      id: 'v1',
      title: 'The sort of a tree',
      panes: [
        { id: 'v', label: 'KcoreSpec/Value.lean', source: sortOf, lang: 'lean' },
        { id: 'w', label: checkedLabel(workedCtor), source: workedCtor, lang: 'lean' },
      ],
      frames: [
        {
          hl: { v: [at(sortOf, 'def sortOf : GroundTerm → Option Srt')] },
          notes: [note('v', at(sortOf, 'def sortOf : GroundTerm → Option Srt'), 'The sort of a ground term, or `none` when it has none.', 'Option Srt')],
          say: 'Not every tree is a value: `s(run(z))` is a ground term, but not one of any sort. `sortOf` decides which trees are values, and of which sort.',
        },
        {
          hl: { v: span(sortOf, '| .ctor f ts =>', '| none => none'), w: span(workedCtor, 'c.sortOf z =', 'c.sortOf (run') },
          notes: [note('v', at(sortOf, 'if sortsOf ts == some k.args'), "A constructor's arguments must have exactly its argument sorts. Then the tree has its result sort.", 'sortsOf ts == some k.args')],
        },
      ],
    },
    {
      id: 'v2',
      title: 'Injections',
      panes: [
        { id: 'v', label: 'KcoreSpec/Value.lean', source: sortOf, lang: 'lean' },
        { id: 'w', label: checkedLabel(workedInj), source: workedInj, lang: 'lean' },
      ],
      frames: [
        {
          hl: { w: [at(workedInj, 'c.sortOf (done z)')] },
          notes: [note('w', at(workedInj, 'c.sortOf (done z)'), '`Val` is not `Nat`: the argument sorts must be equal, not merely related.', 'none')],
        },
        {
          hl: { v: span(sortOf, '| .inj a b t =>', 'else none'), w: span(workedInj, 'c.sortOf (natVal z)', 'c.sortOf (done (natVal z))') },
          notes: [note('v', at(sortOf, '| .inj a b t =>'), 'An injection from `a` to `b` has sort `b` when `a` is below `b` and its term has sort `a`.', 'c.subsorts.contains (a, b)')],
          say: 'So a subsort is used through an explicit injection, never silently.',
        },
        {
          hl: { v: [at(sortOf, '| .inj a b t =>')], w: [at(workedInj, '.inj Srt.«Val»')] },
          notes: [note('v', at(sortOf, '| .inj a b t =>'), 'Never an injection of an injection, so each value is written one way.', '!t.isInj')],
        },
      ],
    },
    {
      id: 'v3',
      title: 'Literals and collections',
      panes: [{ id: 'v', label: 'KcoreSpec/Value.lean', source: sortOf, lang: 'lean' }],
      frames: [
        {
          hl: { v: [at(sortOf, '| .dv s lit =>')] },
          notes: [note('v', at(sortOf, '| .dv s lit =>'), "A literal has its sort when it is of that sort's kind: an Int of `Int`, a Bool of `Bool`.", 'dvOK')],
        },
        {
          hl: { v: span(sortOf, '| .map s es =>', '| some k, some ss => if k.kind == .list') },
          notes: [note('v', at(sortOf, 'keysSorted es'), "A map is a value only with its keys in order, and a set with its elements in order, so equal collections are equal trees.", 'keysSorted es')],
        },
      ],
    },
    {
      id: 'v4',
      title: 'Configurations',
      panes: [
        { id: 'c', label: 'KcoreSpec/Value.lean', source: configDef, lang: 'lean' },
        { id: 'w', label: checkedLabel(workedConfig), source: workedConfig, lang: 'lean' },
      ],
      frames: [
        {
          hl: { c: [at(configDef, 'def Value')] },
          notes: [note('c', at(configDef, 'def Value'), 'A value of sort `s`: a ground term with a proof that its sort is `s`.', '{ t : GroundTerm // c.sortOf t = some s }')],
        },
        {
          hl: { c: [at(configDef, 'abbrev Config')], w: span(workedConfig, '-- the prologue\'s starting', 'some topCellSort') },
          notes: [note('c', at(configDef, 'abbrev Config'), "A configuration: a value of the top cell's sort.", 'topCellSort')],
        },
        {
          hl: { w: span(workedConfig, "-- the prologue's done(s(z))", 'sorted_doneSZ') },
          say: 'The theorems quantify over `Config`, so they speak about every well-sorted configuration, reachable or not, such as the prologue\'s `done(s(z))`.',
        },
      ],
    },
  ],
  quiz: [
    {
      q: 'What is `sortOf done(z)` in peano, with no injection?',
      options: ['`none`', '`some State`', '`some Val`'],
      answer: 0,
      why: '`done` takes a `Val` and `z` is a `Nat`. A constructor needs its argument sorts exactly; `inj{Nat,Val}(z)` is the value of sort `Val`.',
    },
    {
      q: 'Is the prologue\'s `done(s(z))` configuration a `Config`, though no run reaches it?',
      options: ['Yes: it is well sorted, of the top cell\'s sort', 'No: a `Config` must be reachable', 'Only if a rule applies to it'],
      answer: 0,
      why: '`Config` asks only for the sort, so statements about configurations also cover the ones no run reaches.',
    },
  ],
  checked: [
    `The Lean in every pane is kcore-spec's text at \`${coreCommit}\`.`,
    `The panes headed “Checked by Lean” state each sort in Lean; Lean's kernel computed them from peano's package.`,
  ],
}
