'use client'

// Lesson 3: the three parts of `Definition`, the generator `emit`, the constructor fragment (F0) and its
// round trip, and what it rejects. Counts of the emitted KORE and the well-formedness report were computed
// by Lean on peano's data (Facts.lean); the rejection mechanisms are the build's own checked output
// (SpecChecks.lean); the kernel costs are the last run of test/F0Check.lean.

import { fmt, lean, lineOf, source, span } from '../data'
import { type Lesson, note } from '../lesson'
import { numbers } from '../numbers'
import { A, Arrow, Box, Label, Svg } from '../viz'

const defs = source('definitionStruct')
const core = source('PeanoCore')
const pres = source('peanoPres')
const emitHead = source('emitHeader')
const user = source('userModule')
const fragment = source('Fragment')
const parseHead = source('parseHeader')
const f0 = source('f0Check')
const diag = source('witnessDiag')
const reorder = source('reorderedSameModels')
const stats = lean.facts.emit
const kinds = stats.userKinds
const d = lean.f0check.decisions
const f = lean.f0check

if (stats.emptySlices.length) throw new Error(`lean lessons: empty fixed slices ${stats.emptySlices.join(', ')}`)
if (!stats.report.every((r) => r.holds) || !stats.wf) throw new Error('lean lessons: peano is no longer well formed')

const block = (needle: string) => {
  const first = lineOf(diag, needle)
  const rows = diag.text.split('\n')
  const out: number[] = []
  for (let l = first; l <= diag.end; l += 1) {
    const row = rows[l - diag.start]
    if (row.startsWith('-/')) break
    out.push(l)
  }
  return out
}

const loop = (at: number) => (
  <Svg viewBox="0 0 900 430" label="The round trip: a reader turns KORE into a Lean value, emit turns the value back into KORE, and the two texts are compared">
    <Box x={150} y={100} w={210} text="kompile's KORE" />
    <Box x={750} y={100} w={210} text="peano : Definition" sub="a Lean value" tone={at === 0 ? 'on' : 'plain'} />
    <Arrow x1={258} y1={100} x2={640} y2={100} label="a reader (hard, and not reviewed)" on={at === 0} dash />
    <A show={at >= 1}>
      <Box x={750} y={320} w={210} text="emit peano" sub="KORE, generated" tone={at === 1 ? 'on' : 'plain'} />
      <Arrow x1={750} y1={126} x2={750} y2={292} label="emit" on={at === 1} />
    </A>
    <A show={at >= 2}>
      <Arrow x1={640} y1={320} x2={420} y2={320} on={at === 2} />
      <Arrow x1={150} y1={126} x2={320} y2={288} on={at === 2} />
      <Box x={350} y={320} w={130} text="same text?" tone={at === 2 ? 'on' : 'plain'} sans />
    </A>
    <A show={at >= 3}>
      <Label x={350} y={380} anchor="middle" size={14} weight={600} tone="var(--ok)" text="so only emit has to be right" />
      <Label x={350} y={400} anchor="middle" size={12} tone="var(--muted)" text="reviewed once, for every definition" />
    </A>
  </Svg>
)

export const lesson3: Lesson = {
  id: 'the-definition-as-a-value',
  number: 3,
  title: 'The definition as a Lean value',
  scenes: [
    {
      id: 'v1',
      title: 'The idea: a round trip',
      visual: loop,
      frames: [
        { say: "Lesson 2 gave a step its official meaning. To prove things with a proof assistant, the definition has to be something Lean can compute with, a value. Converting KORE into Lean data is hard to get right." },
        { say: "So don't trust the conversion. A generator, `emit`, turns the Lean data back into KORE." },
        { say: "Then compare the result with the text kompile wrote. If the reader got anything wrong, the comparison fails." },
        { say: "That moves the whole burden. The reader needs ==no review==. Only `emit` has to be right, and it is reviewed once for every definition." },
      ],
    },
    {
      id: 'v2',
      title: 'A definition has three parts',
      panes: [
        { id: 'd', label: 'The type', source: defs },
        { id: 'c', label: "peano's core", source: core },
      ],
      frames: [
        { hl: { d: span(defs, 'structure Definition where', 'cert : Certificates') }, notes: [note('d', lineOf(defs, 'structure Definition where'), "A definition is a Lean value of this type, with three fields.")] },
        { hl: { c: span(core, 'def peanoCore : Semantics', 'rhs := tcfg (tdone') }, notes: [note('c', lineOf(core, 'def peanoCore : Semantics'), "Sorts, constructors, functions with their clauses, subsorts, the sort of the program, and the rules.")], say: "The first part is the ==core==: what a step reads. Lesson 4 reads it." },
      ],
    },
    {
      id: 'v3',
      title: 'Presentation and certificate',
      panes: [
        { id: 'd', label: 'The type', source: defs },
        { id: 'p', label: "peano's presentation and the definition", source: pres },
      ],
      frames: [
        { hl: { d: span(defs, 'structure Presentation where', 'initUid : String'), p: span(pres, 'def peanoPres : Presentation', 'initUid :=') }, notes: [note('p', lineOf(pres, 'def peanoPres : Presentation'), "What kompile wrote that a generator cannot recompute: source locations, content hashes, the names of variables it invented, the order productions appeared in.")], say: "The second part is the ==presentation==." },
        {
          hl: { p: [lineOf(pres, `names := ["N", "'Unds'Gen4", "'Unds'DotVar0"]`)] },
          notes: [note('p', lineOf(pres, `names := ["N", "'Unds'Gen4", "'Unds'DotVar0"]`), "The names kompile gave the shared subterm and the counter cell in the first rule.", "'Unds'Gen4")],
          ask: {
            q: "Can the presentation change what a statement about `Step` means?",
            options: ["Yes, source locations are part of a rule", "No: `Step` takes the core only", "Only for definitions with hashes"],
            answer: 1,
            why: "The theory Γ_D is translated from the whole KORE text, so it does read the presentation. That it does not depend on it is stated in the package, not yet proved.",
          },
        },
        { hl: { d: span(defs, 'structure Certificates where', 'decreasing : List (Option Nat)'), p: [lineOf(pres, 'def peano : Definition')] }, notes: [note('d', lineOf(defs, 'structure Certificates where'), "For each function, on which argument its recursive calls decrease."), note('p', lineOf(pres, 'def peano : Definition'), "`pred` makes no recursive call, so peano's certificate is `[none]`.", '[none]')], say: "The third part is the ==certificate==." },
      ],
    },
    {
      id: 'v4',
      title: 'emit: from the value back to KORE',
      panes: [
        { id: 'h', label: 'What emit is', source: emitHead },
        { id: 'u', label: 'The user module it writes', source: user },
      ],
      frames: [
        { hl: { h: span(emitHead, '`emit : Semantics → Presentation', 'the certificate is not emitted.') }, notes: [note('h', lineOf(emitHead, '`emit : Semantics → Presentation'), "From the core and the presentation. It never reads the certificate.")] },
        { hl: { u: span(user, 'sentences :=', '++ fixedSentences "F0-MAP-CEIL"') }, notes: [note('u', lineOf(user, 'sentences :='), "In kompile's order: sort declarations, symbol declarations, the axioms kompile derives from declarations, then equations and rules, then helper equations.")] },
        { hl: { u: user.text.split('\n').map((row, i) => (row.includes('fixedSentences') ? user.start + i : -1)).filter((l) => l > 0) }, notes: [note('u', lineOf(user, 'fixedSentences'), "A slice of fixed KORE, cut from kompile's output once.", 'fixedSentences')], say: "Where the text is the same for every definition, `emit` copies it." },
        { hl: { u: [lineOf(user, '++ (prods c p).flatMap (prodSymbol p)'), lineOf(user, '++ (withPres c.fns p.fns).flatMap'), lineOf(user, '++ (rulesWith c p).map')] }, notes: [note('u', lineOf(user, '++ (prods c p).flatMap (prodSymbol p)'), "one symbol per constructor", 'prodSymbol'), note('u', lineOf(user, '++ (withPres c.fns p.fns).flatMap'), "an equation per clause", 'withPres'), note('u', lineOf(user, '++ (rulesWith c p).map'), "an axiom per rule", 'rulesWith')], say: "Everything else comes from a field of the core." },
        {
          say: "For peano, `emit` writes " + stats.modules.length + " modules. The user module has " + fmt(stats.modules[stats.modules.length - 1].sentences) + " sentences: " + fmt(kinds.sort ?? 0) + " sort declarations, " + fmt(kinds.symbol ?? 0) + " symbol declarations and " + fmt(kinds.axiom ?? 0) + " axioms. " + fmt(stats.fixedInUser) + " of them are fixed text.",
          ask: {
            q: "If `emit` wrote a rule's axiom wrongly, what would happen with peano?",
            options: ["A wrong theorem would become provable", "The KORE it writes would differ from kompile's, the comparison would fail, and peano would not be accepted", "Nothing: the comparison ignores rules"],
            answer: 1,
            why: "A wrong `emit` could only make a correct definition fail, unless it were wrong in exactly the way kompile is.",
          },
        },
      ],
    },
    {
      id: 'v5',
      title: 'The round trip: the constructor fragment',
      panes: [
        { id: 'f', label: 'The constructor fragment, F₀', source: fragment },
        { id: 'r', label: 'The reader', source: parseHead },
      ],
      frames: [
        { hl: { f: span(fragment, 'def F0 (k : Kore.Definition) : Prop :=', '| none => False') }, notes: [note('f', lineOf(fragment, 'def F0 (k : Kore.Definition) : Prop :='), "A reader finds a definition `d` in `k`, `d` is well formed, and `emit d` is `k` up to the order of each module's sentences.")], say: "A KORE text `k` is in the ==constructor fragment==, F₀ (`F0` in Lean), when this holds." },
        { hl: { r: span(parseHead, '`parse : Kore.Definition', 'k is rejected.') }, notes: [note('r', lineOf(parseHead, '`parse : Kore.Definition'), "Not reviewed. Whatever it returns is checked by the other two conditions, so a wrong reader can only reject.")] },
        {
          hl: { f: span(fragment, 'theorem F0.sound', '· exact h.elim') },
          notes: [note('f', lineOf(fragment, 'theorem F0.sound'), "A text in F₀ is the emitted KORE of a well-formed definition. The proof is a case split on what the reader returned.")], say: "`F0.sound` is what a reader of the statements relies on.",
          ask: {
            q: "Which condition of `F0` would catch a reader that dropped one of peano's rules?",
            options: ["Well-formedness", "The comparison: `emit` writes one rule axiom, and kompile's text has two", "None; a dropped rule is invisible"],
            answer: 1,
            why: "A definition missing a rule can be perfectly well formed. It just doesn't generate the text you started from.",
          },
        },
      ],
    },
    {
      id: 'v6',
      title: 'Up to the order of sentences',
      panes: [
        { id: 'f', label: 'The constructor fragment, F₀', source: fragment },
        { id: 'o', label: 'Order has no meaning', source: reorder },
      ],
      frames: [
        { hl: { f: span(fragment, 'def Reordered (e k : Kore.Definition) : Prop :=', 'mm.1.sentences.Perm mm.2.sentences') }, notes: [note('f', lineOf(fragment, 'def Reordered (e k : Kore.Definition) : Prop :='), "The same modules, names and attributes, and in each module the same sentences, counted with repetitions, in any order.")], say: "\"Up to order\" is `Reordered`." },
        { hl: { f: span(fragment, 'def Reordered (e k : Kore.Definition) : Prop :=', 'mm.1.sentences.Perm mm.2.sentences') }, say: "The comparison has been up to order, not exact equality, since 2026-11-07. krust writes some sentences of a definition at positions that depend on the module's name, and exact equality turned that into a reason to reject a definition." },
        { hl: { o: span(reorder, 'theorem reordered_sameModels', 'SameModels (Theory.ofDefinition d.emit)') }, notes: [note('o', lineOf(reorder, 'theorem reordered_sameModels'), "The theories of two reordered texts have the same models.")], say: "The looser comparison costs one theorem, and it's proved. The order of sentences has no meaning in KORE." },
      ],
    },
    {
      id: 'v7',
      title: 'What the kernel checks for peano',
      panes: [
        { id: 'f', label: 'Well-formed', source: fragment },
        { id: 'k', label: 'Kernel checks for peano', source: f0 },
      ],
      frames: [
        { hl: { f: span(fragment, 'def Definition.report', '("presentation: variable names distinct", d.pres.ok d.sem)]') }, notes: [note('f', lineOf(fragment, 'def Definition.report'), "Eight conditions on the definition. For peano Lean computes all eight true.")] },
        { hl: { k: span(f0, 'theorem wf_peano', 'theorem peano_F0') }, say: "For peano the kernel checks more than F₀ needs: `emit peano` equals kompile's KORE ==exactly==, in the same order. In the last run the three checks cost " + fmt(d.wf_peano.kHb) + ", " + fmt(d.emit_peano.kHb) + " and " + fmt(d.peano_F0.kHb) + " thousand heartbeats: " + d.wf_peano.seconds + ", " + d.emit_peano.seconds + " and " + d.peano_F0.seconds + " seconds." },
      ],
    },
    {
      id: 'v8',
      title: 'What F₀ rejects',
      panes: [
        { id: 'w', label: 'Why each is rejected (checked by the build)', source: diag },
        { id: 'k', label: 'The same, as kernel theorems', source: f0 },
      ],
      frames: [
        { hl: { w: block('info: [("m1 drop') }, say: "The package keeps a list of KORE texts that F₀ must reject: mutations of peano's KORE, and the counterexamples two reviews of earlier versions found. The build checks the ==reason== each one is rejected." },
        {
          hl: { w: [lineOf(diag, '("m1 drop'), lineOf(diag, '("m4 owise')] },
          notes: [note('w', lineOf(diag, '("m1 drop'), "Dropping an equation changes the text: some sentence is not one `emit` writes.", '("m1 drop'), note('w', lineOf(diag, '("m4 owise'), "So does adding an `owise` attribute to a rule.", '("m4 owise')],
          ask: {
            q: "Why are most rejections \"not emitted\" rather than a specific error?",
            options: ["`F0` does not look for bad shapes: it accepts exactly what `emit` writes for well-formed data", "Error messages are too costly in the kernel", "The specific errors have not been written yet"],
            answer: 0,
            why: "Anything else, whatever is wrong with it, is some sentence `emit` does not write.",
          },
        },
        { hl: { w: [lineOf(diag, '("m2 second')] }, notes: [note('w', lineOf(diag, '("m2 second'), "It overlaps the first, and `wf` rejects it: functions must be deterministic.", '("m2 second')] },
        { hl: { w: [lineOf(diag, '("m3 pred'), lineOf(diag, '("R1-3 decreasing')] }, notes: [note('w', lineOf(diag, '("m3 pred'), "A recursive call that does not decrease: `wf` rejects it, through the certificate.", '("m3 pred')] },
        { hl: { w: [lineOf(diag, '("R1-6c [assoc]'), lineOf(diag, '("R1-6b [functional]')] }, notes: [note('w', lineOf(diag, '("R1-6c [assoc]'), "An axiom that would make the theory say something false, such as `⊤Bool = ⊥Bool`. Rejected because `emit` never writes it.", '("R1-6c [assoc]')] },
        { hl: { k: span(f0, 'theorem m1_not_F0', 'theorem w5ok_F0') }, say: "Each rejection, and three repaired versions that F₀ accepts, is also a theorem the kernel checked: " + f.rejections + " rejections and " + f.controls + " acceptances, " + fmt(f.rejectionKHb) + " thousand heartbeats in all." },
        { say: "All of this is the constructor fragment, which fits peano and little else. The builtin fragment, F₁, has the same three-part `Definition`, the same `emit`-and-compare check and the same comparison up to sentence order, over a larger language: several cells, Bool and Int, `requires`, maps. [Lesson 9](/lean/beyond-peano) takes a definition through it." },
      ],
    },
  ],
  quiz: [
    {
      q: "Why keep hashes and source locations at all, if no step reads them?",
      options: ["To reproduce kompile's KORE exactly, since the comparison does no renaming or normalization", "To speed up the kernel", "For error messages"],
      answer: 0,
      why: "Without them `emit` could not give back the text that the round trip compares against.",
    },
    {
      q: "Why is it `emit`, from Lean to KORE, that has to be reviewed, and not a reader from KORE to Lean?",
      options: ["`emit` is shorter by luck", "A reader's output is checked by running `emit` on it and comparing with the input, so only the direction that is compared against has to be right", "Readers cannot be written in Lean"],
      answer: 1,
      why: "That's the whole point of the round trip.",
    },
    {
      q: "Why is comparing up to order enough, when exact equality was possible for peano?",
      options: ["Exact equality would reject some definitions for a reason that changes no axiom, and `reordered_sameModels` shows the looser comparison loses nothing", "Exact equality is too expensive to check", "Peano's text is not ordered"],
      answer: 0,
      why: "krust writes some sentences in an order that depends on module names.",
    },
    {
      q: "What would it take to make F₀ accept a wrong axiom?",
      options: ["A wrong reader", "A well-formed definition whose `emit` writes it", "A very long KORE file"],
      answer: 1,
      why: "That is a question about `emit`'s text, read once for every definition. Lesson 6 counts its lines.",
    },
  ],
  checked: [
    "`F0.sound`, `reordered_sameModels` and the proofs of this lesson use only the axioms `propext`, `Classical.choice` and `Quot.sound`; the build pins their axiom lists.",
    "For peano, kernel decisions: `wf peano`, `peano.emit = kore` (exact equality with kompile's KORE), and `F0 kore`. They are in `test/F0Check.lean`, outside the default build: its last run took " + numbers.f0Minutes + " minutes and " + numbers.f0Gb + " GiB of memory.",
    "The " + numbers.f0Rejections + " rejections and " + numbers.f0Controls + " acceptances are kernel decisions in the same file. The reason each is rejected is a compiled check in the default build, so a change of reason fails the build.",
    "Not checked: that `emit` writes, for other definitions, the text krust's kompile writes. That's a question of coverage, not soundness: a definition `emit` cannot reproduce is rejected, never misread.",
  ],
  tryit: [
    { say: "In the kcore-spec package directory:", cmd: "lake build                        # includes the compiled checks of every rejection's reason\nlake env lean test/F0Check.lean   # the kernel decisions (heavy: see above)" },
  ],
}
