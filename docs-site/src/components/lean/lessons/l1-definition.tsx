'use client'

// Lesson 1: peano.k, the KORE kompile writes for it, a run of it with krust, and what a run cannot
// show. The KORE is kompile's output; the run is krust's output, captured by the generator's krun
// script; the extra configurations and their successors were computed by Lean on the package's
// data (Facts.lean).

import { type Ground, config, fmt, groundText, kItem, koreAxiom, lean, lineOf, peanoK, peanoLines, span, textSource } from '../data'
import { type Lesson, note } from '../lesson'
import { A, Arrow, Box, Label, Svg } from '../viz'

const k = peanoK
const rule0 = koreAxiom('rule', 0)
const eq0 = koreAxiom('equation', 0)
const eq1 = koreAxiom('equation', 1)
// The two equations in one pane, the attribute lines between them elided.
const eqs = { ...eq0, end: eq1.end, text: [eq0.text, ...Array(eq1.start - eq0.end - 1).fill('…'), eq1.text].join('\n') }
const emit = lean.facts.emit
const userModule = emit.modules[emit.modules.length - 1]
const totalSentences = emit.modules.reduce((sum, m) => sum + m.sentences, 0)

if (userModule.name !== 'PEANO') throw new Error('lean lessons: the last emitted module is not PEANO')
if (!emit.reordered) throw new Error('lean lessons: the emitted KORE is no longer kompile’s for peano, up to the order of sentences')

const runs = lean.krun.steps
const out = (d: number) => {
  const found = runs.find((r) => r.depth === d)
  if (!found) throw new Error(`lean lessons: no krun output at depth ${d}`)
  return textSource(`krust krun … --depth ${d}`, found.text)
}
if (out(3).text !== out(4).text) throw new Error('lean lessons: the run did not stop after three steps')
const outLine = (d: number, needle: string) => [lineOf(out(d), needle)]

const runTerms = ['run(s(s(z)))', 'run(s(z))', 'run(z)', 'done(z)'] as const
const runChain = (at: number) => {
  const reached = Math.min(at, 3)
  return (
    <Svg viewBox="0 0 460 420" label="The run so far">
      {runTerms.map((term, i) => (
        <A key={term} show={i <= reached}>
          <Box x={230} y={50 + i * 100} w={220} text={term} sub={`depth ${i}`} tone={i === reached ? 'on' : 'plain'} />
          {i < 3 && <A show={i < reached}><Arrow x1={230} y1={76 + i * 100} x2={230} y2={122 + i * 100} on={i === reached - 1} label="one step" /></A>}
        </A>
      ))}
      <A show={at >= 4}>
        <Label x={380} y={356} text="no rule applies" tone="var(--bad)" size={12} anchor="middle" weight={600} />
        <Label x={380} y={372} text="depth 4 prints the same" tone="var(--muted)" size={11} anchor="middle" />
      </A>
    </Svg>
  )
}

const c0 = config('c0')
const c1 = config('c1')
const c2 = config('c2')
const c3 = config('c3')
const kc = config('kconfig')
const showTerm = (g: Ground) => {
  try {
    return groundText(kItem(g))
  } catch {
    return groundText(g)
  }
}
if ((c3.successors ?? [1]).length !== 0 || (kc.successors ?? [1]).length !== 0) throw new Error('lean lessons: done(s(z)) and the #KConfigValue configuration are no longer stuck')
if (showTerm(c0.term) !== 'run(s(z))' || showTerm(c1.term) !== 'run(z)' || showTerm(c2.term) !== 'done(inj{SortNat,SortVal}(z))' && showTerm(c2.term) !== 'done(inj{Nat,Val}(z))') {
  throw new Error(`lean lessons: the configurations of the first lesson changed: ${showTerm(c2.term)}`)
}

const beyond = (at: number) => (
  <Svg viewBox="0 0 900 430" label="The configurations of one run, and others no run reaches">
    <Label x={40} y={46} text="WHAT THE RUN VISITED" size={11} tone="var(--muted)" isMono />
    {runTerms.map((term, i) => (
      <g key={term}>
        <Box x={130 + i * 215} y={90} w={170} text={term} tone={at === 0 ? 'accent' : 'plain'} />
        {i < 3 && <Arrow x1={215 + i * 215} y1={90} x2={260 + i * 215} y2={90} on={at === 0} />}
      </g>
    ))}
    <A show={at >= 1}>
      <Label x={40} y={176} text="CONFIGURATIONS NO RUN REACHES" size={11} tone="var(--muted)" isMono />
      <Box x={130} y={222} w={170} text={showTerm(c3.term).replace(/inj\{[^}]*\}\((.*)\)\)$/, '$1)')} sub="next: none" tone={at === 1 ? 'on' : 'plain'} />
    </A>
    <A show={at >= 2}>
      <Box x={410} y={222} w={300} text={showTerm(kc.term).replace('dotk', '.K')} sub="next: none" tone={at === 2 ? 'on' : 'plain'} size={12} />
    </A>
    <A show={at >= 3}>
      <Box x={700} y={222} w={230} text="…infinitely many more" tone={at === 3 ? 'on' : 'ghost'} dash sans />
    </A>
    <A show={at >= 4}>
      <rect x={30} y={300} width={840} height={100} rx={10} fill="var(--gold-tint)" stroke="var(--gold)" />
      <Label x={450} y={340} anchor="middle" size={17} weight={600} text="“A configuration has at most one next one.”" />
      <Label x={450} y={370} anchor="middle" size={17} weight={600} text="“The counter cell never changes.”" />
    </A>
  </Svg>
)

export const lesson1: Lesson = {
  id: 'a-definition-and-its-steps',
  number: 1,
  title: 'A definition and its steps',
  scenes: [
    {
      id: 'd1',
      title: 'What you wrote',
      panes: [{ id: 'k', label: 'peano.k', source: k, lang: 'k' }],
      frames: [
        { say: `You wrote a K definition, compiled it and ran a program. The run printed the configurations you expected. This lesson looks at what that shows, and at the gap a proof has to fill. Here's the definition again: ${peanoLines} lines.` },
        { hl: { k: [lineOf(k, 'rule <k> run(s(N))')] }, notes: [note('k', lineOf(k, 'rule <k> run(s(N))'), "When the k cell holds `run(s(N))`, replace it by `run(pred(s(N)))`.")], say: "Follow this rule. It mentions one cell and two uses of `s(N)`." },
        { hl: { k: [lineOf(k, 'configuration')] }, say: 'A K definition isn\'t run as written. kompile translates it into ==KORE==, a small logical language: sort and symbol declarations, and axioms. The backends that run programs read KORE, and so does everything in this series.' },
      ],
    },
    {
      id: 'd2',
      title: 'A rule becomes an axiom',
      panes: [
        { id: 'k', label: 'peano.k', source: k, lang: 'k' },
        { id: 'r', label: 'What kompile wrote', source: rule0, lang: 'kore' },
      ],
      frames: [
        { hl: { k: [lineOf(k, 'rule <k> run(s(N))')] }, say: 'On the right is the real KORE axiom kompile wrote for that one rule. It looks like much more than the rule, so go through what it added.' },
        {
          hl: { k: [lineOf(k, 'rule <k> run(s(N))')], r: [lineOf(rule0, '\\rewrites'), lineOf(rule0, "Lbl'-LT-'generatedTop'-GT-'"), lineOf(rule0, "Var'Unds'DotVar0")] },
          notes: [note('r', lineOf(rule0, '\\rewrites'), "One rewrite axiom…", '\\rewrites'), note('r', lineOf(rule0, "Lbl'-LT-'generatedTop'-GT-'"), "…over the whole configuration: the top cell, the k cell…", "Lbl'-LT-'generatedTop'-GT-'"), note('r', lineOf(rule0, "Var'Unds'DotVar0"), "…and a counter cell your source never mentions.", "Var'Unds'DotVar0")],
          ask: {
            q: 'Your rule mentions only the k cell. Why does its axiom mention a counter cell at all?',
            options: ['The counter is incremented by every rule', 'A rule rewrites a whole configuration, so kompile completes it with the cells it leaves out, as variables that copy them unchanged', 'It is a debugging aid that backends ignore'],
            answer: 1,
            why: 'The variable `DotVar0` appears on both sides, so the cell passes through unchanged. Lesson 4 turns that observation into a proved invariant.',
          },
        },
        { hl: { k: [lineOf(k, 'rule <k> run(s(N))')], r: [lineOf(rule0, 'VarN'), lineOf(rule0, 'Lblpred')] }, notes: [note('r', lineOf(rule0, 'VarN'), "The two copies of `s(N)` became one shared subterm: `\\and` of the pattern and a fresh variable.", '\\and'), note('r', lineOf(rule0, 'Lblpred'), "The right-hand side reuses that variable.", "Var'Unds'Gen4")] },
      ],
    },
    {
      id: 'd3',
      title: 'Equations become implications',
      panes: [
        { id: 'k', label: 'peano.k', source: k, lang: 'k' },
        { id: 'e', label: 'The equations of pred', source: eqs, lang: 'kore' },
      ],
      frames: [
        { hl: { k: [lineOf(k, 'rule pred(s(N))')], e: span(eqs, 'axiom{R}', 'Lblpred', eq0.start - 1) }, notes: [note('e', lineOf(eqs, 'axiom{R}', eq0.start - 1), "Applies when the argument is `s(N)`.")], say: "A function's equations become axioms too, each an implication whose premise says when it applies." },
        {
          hl: { k: [lineOf(k, 'rule pred(_)')], e: [lineOf(eqs, '\\not')] },
          notes: [note('e', lineOf(eqs, '\\not'), "The negation of the first equation's premise: this applies exactly when no other equation does.", '\\not')],
          ask: {
            q: 'Why a negation, and not an attribute that says "try this one last"?',
            options: ['An attribute would be too slow to check', 'A KORE axiom is a logical statement, read without any order, so "last" has to be written as a condition', 'Attributes are not allowed on KORE axioms'],
            answer: 1,
            why: 'Axioms in a theory have no order. This is why lesson 2 can compare two KORE texts up to the order of their sentences.',
          },
        },
        { say: `For these ${peanoLines} lines, kompile writes ${emit.modules.length} modules and ${fmt(totalSentences)} sentences. The module \`PEANO\` alone has ${fmt(userModule.sentences)}, and ${fmt(emit.fixedInUser)} of those are the same text in every definition with the same imports.` },
      ],
    },
    {
      id: 'd4',
      title: 'A run, as krust prints it',
      visual: runChain,
      panes: [{ id: 'r', label: 'The configuration', source: out(0), lang: 'kore' }],
      frames: [
        { hl: { r: outLine(0, 'Lblrun') }, text: { r: out(0) }, notes: [note('r', outLine(0, 'Lblrun')[0], "The program, in the k cell.", 'Lblrun'), note('r', lineOf(out(0), 'generatedCounter'), "The counter, at 0.", '\\dv{SortInt{}}')], say: "krust runs the definition on `run(s(s(z)))`. With `--depth 0` it shows the starting configuration." },
        { hl: { r: outLine(1, 'Lblrun') }, text: { r: out(1) }, notes: [note('r', outLine(1, 'Lblrun')[0], "After one step: `run(s(z))`.", 'Lblrun')], say: "The rule wrote `run(pred(s(s(z))))`, and evaluating `pred` is part of the same step." },
        { hl: { r: outLine(2, 'Lblrun') }, text: { r: out(2) }, notes: [note('r', outLine(2, 'Lblrun')[0], "After two steps: `run(z)`.", 'Lblrun')] },
        { hl: { r: outLine(3, 'Lbldone') }, text: { r: out(3) }, notes: [note('r', outLine(3, 'Lbldone')[0], "After three: `done(z)`.", 'Lbldone'), note('r', outLine(3, 'Lbldone')[0], "`done` takes a `Val` and `z` is a `Nat`, so `z` sits under an injection.", 'inj{SortNat{}, SortVal{}}')] },
        {
          hl: { r: outLine(4, 'Lbldone') },
          text: { r: out(4) },
          say: 'Asking for four steps gives the same configuration. No rule applies to `done(z)`, so the run stops.',
          ask: {
            q: 'Did this run use the `[owise]` equation of `pred`?',
            options: ['Yes, at the last step, on `pred(z)`', 'No: every call was `pred(s(…))`, which the first equation answers', 'Yes, at every step'],
            answer: 1,
            why: "The rule only writes `pred` around `s(N)`, so peano's rules never reach `pred(z)`. A run can't tell you the `[owise]` equation is right. That's a first hint of what's missing.",
          },
        },
      ],
    },
    {
      id: 'd5',
      title: 'What a run cannot show',
      visual: beyond,
      frames: [
        { say: 'A run visits one path. These are the four configurations this one visited, in a line.' },
        { say: "`done(s(z))` is a configuration too. No rule writes it, so no run from a program of the form `run(n)` reaches it. The package's step function, which lesson 3 explains, computes that it has no next configuration." },
        { say: 'The fixed signature of every kompiled definition adds configurations no program writes, such as a k cell holding `#KConfigValue(.K)`.' },
        { say: 'And there are infinitely many more. A second run of the same program would show the same three steps. It says nothing about other inputs.' },
        {
          say: 'These two claims are about ==all== of those. A run cannot establish them. A proof can, once "next" has a precise meaning.',
          ask: {
            q: 'Why should a statement about peano care about `done(s(z))`, if no run reaches it?',
            options: ['Reachability is itself a property that needs proof; a statement over every configuration needs no such proof first', 'Because `done(s(z))` is secretly reachable', 'It should not: statements should only cover reachable configurations'],
            answer: 0,
            why: "A statement over every configuration also stays true for a program you didn't think of.",
          },
        },
        { say: 'Two questions follow. ==What is a step==, precisely enough that a proof can quantify over all of them? And ==why should anyone believe== a proof about that definition is a proof about `peano.k`? The rest of the series answers both.' },
      ],
    },
  ],
  quiz: [
    {
      q: 'What exactly does kompile add to a K rule that mentions only the k cell?',
      options: ['Nothing; it copies the rule', 'The rest of the configuration, as variables, so that the rule rewrites the whole configuration', 'A proof that the rule terminates'],
      answer: 1,
      why: 'The rule becomes one `\\rewrites` axiom over the whole configuration, with the cells it leaves out as variables.',
    },
    {
      q: 'What would a second run on the same program show?',
      options: ['The same three steps: a run is a computation on one input', 'Other paths through the definition', 'A proof that the definition is deterministic'],
      answer: 0,
      why: 'It says nothing about other inputs.',
    },
  ],
  checked: [
    "The KORE in these scenes is kompile's output for `peano.k`, as krust's kompile wrote it. Lesson 2 shows the package's Lean definition generates this KORE, up to the order of its sentences, a fact the Lean kernel checks.",
    "The run is krust's output for this program, captured when the page's data was generated.",
    "The next configurations in the last scene were computed by the package's executable step function. Lesson 3 shows it lists exactly the successors of the step relation.",
    "Not checked: that kompile's KORE means what `peano.k` means. kompile is trusted, and the overview says so.",
  ],
  tryit: [
    {
      say: 'From a checkout of the k-rust repository, with krust built (`cargo build --release -p k-rust`), in a directory holding `peano.k`:',
      cmd: "krust krun -m PEANO -s State -e 'run(s(s(z)))' --depth 3 peano.k   # done(z)\nkrust kcompile peano.k --main-module PEANO -o kore                 # the KORE of the first scenes",
    },
  ],
}
