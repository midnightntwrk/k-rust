'use client'

// Lesson 2: the Lean package `kcore gen` writes for peano's KORE: the definition as a term, its
// symbols as numbers, a rule as data, and the tie that makes the term peano's KORE. Every pane is
// a file of the generated package or an excerpt of KCore; the facts are compiled Lean on KCore's
// parse of the same KORE file (Facts.lean); the costs are the package build's.

import { build, fmt, koreAxiom, lean, lineOf, slice, source, span } from '../data'
import { type Lesson, note } from '../lesson'
import { A, Arrow, Box, Label, Rows, Svg } from '../viz'

const core = slice(source('pkgCore'), 'namespace Peano', 'end Peano')
const names = slice(source('pkgNames'), 'namespace Sym', 'end Peano')
const surface = slice(source('pkgSurface'), '/-! ## The rules -/', 'end Peano')
const tieFile = slice(source('pkgTie'), 'theorem tied', 'end Peano')
const semantics = source('coreSemantics')
const regSyms = source('regSyms')
const tied = source('tied')
const reordered = source('reordered')
const sc = source('soundAndComplete')
const rule0 = koreAxiom('rule', 0)

const { registry, emit } = lean.facts
const pkg = lean.package
const ownSym = (name: string) => registry.syms + registry.ownSyms.indexOf(name)
if (registry.ownSyms.indexOf('Lbls') < 0 || !source('pkgNames').text.includes(`«s» : KCore.Sym := ${ownSym('Lbls')}`)) {
  throw new Error('lean lessons: the number of s in Names.lean is not its place in the own symbols')
}
if (!emit.wf || !emit.reordered || emit.report.some((r) => !r.holds)) throw new Error('lean lessons: peano is no longer well formed and tied')
if (lean.facts.rules.length !== 2 || lean.facts.rules.some((r) => r.prio !== 50)) throw new Error('lean lessons: peano no longer has two rules of priority 50')

const seconds = (mods: readonly string[]) => mods.reduce((sum, m) => sum + build(m).seconds, 0)
const peakGb = (mods: readonly string[]) => (Math.max(...mods.map((m) => build(m).rssMiB)) / 1024).toFixed(1)
const facts = pkg.modules.filter((m) => m.startsWith('Peano.Facts.'))
const kinds = pkg.modules.filter((m) => m.startsWith('Peano.Kinds.'))

// The package: what `kcore gen` writes (left), what you write (right).
const packageMap = (at: number) => {
  const lit = (n: number) => (at === n ? 'on' : 'plain')
  const muted = 'var(--muted)'
  return (
    <Svg viewBox="0 0 900 470" label="The package kcore gen writes from definition.kore: Core holds the definition as a term; Names its symbols' names; Facts the decisions the kernel checks; Surface step_iff and the rules as data; Kinds the theorems; Tie that the term is the KORE. Your package imports it: Statements, Facts, Proofs and Cert.">
      <Label x={40} y={34} text="WRITTEN BY kcore gen" size={11} tone={muted} isMono />
      <Box x={140} y={80} w={200} text="definition.kore" sub="kompile's, lesson 1" tone={at === 0 ? 'accent' : 'plain'} />
      <Arrow x1={240} y1={80} x2={330} y2={80} label="kcore gen" on={at === 0} />
      <A show={at >= 1}>
        <Box x={450} y={80} w={220} text="Peano.Core" sub="the definition, as a term" tone={lit(1)} />
        <Box x={450} y={160} w={220} text="Peano.Names" sub="readable names" tone={lit(2)} />
      </A>
      <A show={at >= 3}>
        <Box x={450} y={240} w={220} text="Peano.Facts" sub={`${facts.length} decisions the kernel checks`} tone={lit(3)} />
        <Box x={450} y={320} w={220} text="Peano.Surface" sub="the rules as data, step_iff" tone={lit(3)} />
        <Box x={450} y={400} w={220} text="Peano.Kinds" sub={`${kinds.length} theorems, lesson 4`} tone={lit(3)} />
        <Arrow x1={450} y1={103} x2={450} y2={137} />
        <Arrow x1={450} y1={183} x2={450} y2={217} />
        <Arrow x1={450} y1={263} x2={450} y2={297} />
        <Arrow x1={450} y1={343} x2={450} y2={377} />
      </A>
      <A show={at >= 4}>
        <Box x={180} y={240} w={200} text="Peano.Tie" sub="the term is the KORE" tone={at === 4 ? 'gold' : 'plain'} />
        <Arrow x1={160} y1={103} x2={170} y2={217} on={at === 4} />
        <Arrow x1={340} y1={90} x2={262} y2={217} on={at === 4} dash />
      </A>
      <A show={at >= 5}>
        <Label x={660} y={34} text="WRITTEN BY YOU" size={11} tone={muted} isMono />
        <Box x={760} y={240} w={190} text="User.Statements" sub="what you claim" tone={lit(5)} />
        <Box x={760} y={320} w={190} text="User.Proofs" sub="lesson 4" tone={lit(5)} />
        <Arrow x1={560} y1={400} x2={665} y2={330} on={at === 5} />
        <Arrow x1={760} y1={263} x2={760} y2={297} />
      </A>
    </Svg>
  )
}

const reportRows = () => (
  <Rows
    head={['What wf checks', 'peano']}
    rows={emit.report.map((r) => ({ key: r.condition, cells: [r.condition, r.holds ? 'holds' : 'fails'] }))}
  />
)

const tieCost = () => (
  <Rows
    head={['Part of the package', { text: 'modules', num: true }, { text: 'seconds', num: true }, { text: 'peak GB', num: true }]}
    rows={[
      { key: 'pkg', cells: ['everything but the tie', pkg.modules.length, seconds(pkg.modules).toFixed(0), peakGb(pkg.modules)] },
      { key: 'tie', cells: ['the tie', pkg.tie.length, seconds(pkg.tie).toFixed(0), peakGb(pkg.tie)], state: 'cur' },
      { key: 'user', cells: ['your statements and proofs', pkg.user.length, seconds(pkg.user).toFixed(0), peakGb(pkg.user)] },
    ]}
  />
)

const lhs = lineOf(surface, 'lhs :=')
const rhs = lineOf(surface, 'rhs :=')
const vars = lineOf(surface, 'vars :=')
const prio = lineOf(surface, 'prio := 50')

export const lesson2: Lesson = {
  id: 'the-definition-in-lean',
  number: 2,
  title: 'The definition in Lean',
  scenes: [
    {
      id: 'p1',
      title: 'A generated package',
      visual: packageMap,
      frames: [
        { say: "Lesson 1 ended on two questions. This lesson answers the second: why a Lean definition is peano's definition. One command, `kcore gen`, reads kompile's KORE and writes a Lean package." },
        { say: '`Core` holds the definition itself, as a Lean term.' },
        { say: "`Names` gives its symbols and sorts readable names." },
        { say: 'The rest is about that term: decisions the kernel checks, readable facts about the rules, and the theorems lesson 4 uses.' },
        { say: '`Tie` connects the term back to the KORE text. Without it, nothing says the term is peano.' },
        {
          say: 'Your own package imports the generated one, and holds only your statements and their proofs. Nothing in the generated package is edited by hand.',
          ask: {
            q: 'The generator computes things about peano, such as its tables and which pairs of rules to compare. Do you have to trust those computations?',
            options: ['Yes, the generator is part of what you trust', 'No: each one enters the package as data a kernel decision checks, so a wrong computation fails the build', 'Only for definitions larger than peano'],
            answer: 1,
            why: "A wrong table or a missing pair makes a decision false, and `decide +kernel` fails. The generator can be wrong; the package can't then build.",
          },
        },
      ],
    },
    {
      id: 'p2',
      title: 'The definition is a term',
      panes: [
        { id: 'c', label: 'Peano/Core.lean', source: core, lang: 'lean' },
        { id: 's', label: 'KcoreSpec/Core.lean', source: semantics, lang: 'lean' },
      ],
      frames: [
        { hl: { c: [lineOf(core, 'definition_of defn from')] }, notes: [note('c', lineOf(core, 'definition_of defn from'), "A command reads the KORE file, runs KCore's `parse` on it, and adds the result as a Lean term. The term is never printed.", 'definition_of')] },
        { hl: { c: [lineOf(core, 'noncomputable abbrev c')], s: [lineOf(semantics, 'structure Semantics where')] }, notes: [note('c', lineOf(core, 'noncomputable abbrev c'), 'The part a step reads: the semantics.', 'defn.sem')], say: 'A definition has three parts. The ==semantics== is what steps read.' },
        { hl: { s: [lineOf(semantics, 'ctors : List CtorSig'), lineOf(semantics, 'fns : List Fn'), lineOf(semantics, 'rules : List Rule'), lineOf(semantics, 'config : List Cell')] }, notes: [note('s', lineOf(semantics, 'rules : List Rule'), "peano's two rules, as data.", 'rules'), note('s', lineOf(semantics, 'fns : List Fn'), '`pred`, with its clauses.', 'fns'), note('s', lineOf(semantics, 'config : List Cell'), 'The cells: for peano, one k cell.', 'config')] },
        { say: "The other two parts are what kompile wrote that a step doesn't read, such as attribute lists, variable names and source locations, which printing the KORE back needs; and, for each function, the argument its recursive calls make smaller." },
      ],
    },
    {
      id: 'p3',
      title: 'Symbols are numbers',
      panes: [
        { id: 'n', label: 'Peano/Names.lean', source: names, lang: 'lean' },
        { id: 'g', label: 'KcoreSpec/FixedSignature.lean', source: regSyms, lang: 'lean' },
      ],
      frames: [
        { hl: { n: [lineOf(names, 'def «s» : KCore.Sym')] }, notes: [note('n', lineOf(names, 'def «s» : KCore.Sym'), `In the term, \`s\` is the number ${ownSym('Lbls')}.`, `${ownSym('Lbls')}`)], say: 'In the term, a symbol or a sort is a number. `Names` gives the numbers readable names, so the files that follow can say `s` and `Nat`.' },
        { hl: { g: [lineOf(regSyms, 'def nRegSyms')] }, notes: [note('g', lineOf(regSyms, 'def nRegSyms'), `Below ${registry.syms}: the registry. First K's own symbols, such as \`kseq\` and the top cell, then those of K's builtin modules, such as the integers'. They have the same number in every definition.`, 'nRegSyms')], say: `A definition's own symbols are numbered from ${registry.syms}, and its own sorts, likewise, from ${registry.sorts}. peano has ${registry.ownSyms.length} own symbols: its constructors and \`pred\`, its k cell's, and a sort predicate for each own sort.` },
        { hl: { n: span(names, 'theorem names_ok', 'decide +kernel') }, notes: [note('n', lineOf(names, 'decide +kernel'), "The kernel checks the names against the KORE's.", 'decide +kernel')], say: 'The names are kept for printing. Nothing that decides a property or takes a step compares names. It compares numbers, which is what makes large definitions affordable.' },
        { hl: { n: span(names, 'def «kPath»', 'def get_generatedCounter') }, notes: [note('n', lineOf(names, 'def counterPath'), "Where the counter cell sits in a configuration. Lesson 4 proves every step keeps what is there.", 'counterPath')] },
      ],
    },
    {
      id: 'p4',
      title: 'A rule, as data',
      panes: [
        { id: 'r', label: 'What kompile wrote', source: rule0, lang: 'kore' },
        { id: 's', label: 'Peano/Surface.lean', source: surface, lang: 'lean' },
      ],
      frames: [
        { hl: { s: span(surface, 'kernel_rfl rule0', 'prio := 50') }, say: "Here is lesson 1's first rule again: kompile's axiom on the left, and rule 0 of the term on the right." },
        {
          hl: { r: [lineOf(rule0, "Lbl'-LT-'generatedTop'-GT-'{}("), lineOf(rule0, 'inj{SortState{}, SortKItem{}}(')], s: [lhs] },
          notes: [note('s', lhs, 'The top cell, the k cell and the K sequence, as on the left…', '.app KCore.topLabel'), note('s', lhs, '…with `run(…)` injected from `State` into `KItem`.', '.inj Peano.Srt.«State» KCore.Srt.kitem')],
        },
        {
          hl: { r: [lineOf(rule0, 'Lblrun{}(\\and')], s: [lhs] },
          notes: [note('r', lineOf(rule0, 'Lblrun{}(\\and'), "`s(N)`, shared with a fresh variable.", '\\and'), note('s', lhs, 'The same thing as an alias: `N` is variable 0, and the whole `s(N)` is variable 1.', '.as (.app Peano.Sym.«s» [(.var 0)]) 1')],
        },
        {
          hl: { r: [lineOf(rule0, "Var'Unds'DotVar0")], s: [lhs, rhs] },
          notes: [note('s', lhs, 'The counter cell is variable 2…', '(.var 2)]'), note('s', rhs, '…and the right-hand side puts it back unchanged.', '(.var 2)]')],
        },
        { hl: { s: [vars, prio] }, notes: [note('s', vars, "Each variable's sort, by number: `N` and `s(N)` are `Nat`s.", 'vars :='), note('s', prio, "No priority attribute, so K's default: 50.", 'prio := 50')], say: 'A rule also has a ==priority==. A rule applies only when no rule of a smaller priority does; lesson 3 makes that precise.' },
        {
          hl: { s: [lineOf(surface, 'kernel_rfl rule0')] },
          notes: [note('s', lineOf(surface, 'kernel_rfl rule0'), 'A theorem: the kernel computed rule 0 of the term and found this.', 'kernel_rfl')],
          ask: {
            q: 'The term itself is never printed. What does `rule0` tell you about it?',
            options: ['Nothing; it is a comment', 'Its rule 0 is exactly this, because the kernel checked the equation', 'That printing the term would give this text'],
            answer: 1,
            why: 'The readable form is a checked equation about the term, not a rendering of it. A wrong readable form fails the build.',
          },
        },
        { hl: { s: span(surface, 'kernel_rfl «fn_pred_0»', 'rhs := (.var 0) }') }, notes: [note('s', lineOf(surface, 'kernel_rfl «fn_pred_0»'), "`pred`'s first clause: `pred(s(N)) = N`. Its `[owise]` clause is separate, in `fn_pred_sig`.", 'fn_pred_0')] },
      ],
    },
    {
      id: 'p5',
      title: "Why the term is peano's",
      panes: [
        { id: 't', label: 'KcoreSpec/Tie.lean', source: tied, lang: 'lean' },
        { id: 'o', label: 'KcoreSpec/Kore/Reorder.lean', source: reordered, lang: 'lean' },
      ],
      frames: [
        { say: "Turning KORE into a definition is easy to get wrong. So the package doesn't trust KCore's `parse`. It prints the definition back as KORE and compares the result with kompile's text." },
        { hl: { t: span(tied, 'def Tied', '| none => False') }, notes: [note('t', lineOf(tied, 'match Parse.parse k with'), 'Turn the KORE into a definition…', 'Parse.parse k'), note('t', lineOf(tied, '| some d =>'), '…the result is well formed, and printing it back gives the text.', 'KoreAML.Reordered d.emit k')] },
        { hl: { o: span(reordered, 'def Reordered', 'mm.1.name = mm.2.name') }, notes: [note('o', lineOf(reordered, 'mm.1.sentences.Perm mm.2.sentences'), "The same sentences in each module, in any order.", 'Perm')], say: "The comparison ignores the order of sentences in a module. Lesson 1 showed why it may: axioms have no order. For peano, the printed text has kompile's sentences in another order." },
        { say: "So if `parse` got anything wrong, printing would not give kompile's text back, and the comparison would fail. Only the printer, `emit`, has to be right, and it is written once for every definition." },
      ],
    },
    {
      id: 'p6',
      title: 'The tie, for peano',
      panes: [{ id: 't', label: 'Peano/Tie.lean', source: tieFile, lang: 'lean' }],
      visual: (at) => (at < 2 ? reportRows() : tieCost()),
      frames: [
        { hl: { t: [lineOf(tieFile, 'theorem tied')] }, notes: [note('t', lineOf(tieFile, 'theorem tied'), "`kore` is the KORE file as a Lean term. Three facts the kernel checked make the proof: the term is `parse kore`, it is well formed, and its `emit` is `kore` up to order.", 'KCore.Tied kore')] },
        { say: `Well formed means each of these ${emit.report.length} conditions holds. They are what the theorems about every definition assume.` },
        { say: `The tie is the most expensive part of the package: the kernel runs \`parse\` and the printer on the whole text. It is split into ${pkg.tie.length} modules, each a small decision about a part of the text: ${seconds(pkg.tie).toFixed(0)} seconds in all, at most ${peakGb(pkg.tie)} GB, against ${seconds(pkg.modules).toFixed(0)} seconds for the rest of the package.` },
        { hl: { t: span(tieFile, '#eval show Lean.CoreM Unit', 'throwError "axioms: {axs}"') }, notes: [note('t', lineOf(tieFile, '#eval show Lean.CoreM Unit'), 'The build fails unless the proof uses only Lean\'s three standard axioms.', '#eval')] },
      ],
    },
    {
      id: 'p7',
      title: 'What the tie does not say',
      panes: [{ id: 'a', label: 'KcoreSpec/Statements.lean', source: sc, lang: 'lean' }],
      frames: [
        { say: "The tie says the term is peano's KORE. It doesn't say that `Step`, the relation lesson 3 defines from the term, is what that KORE means." },
        { say: "A KORE text has a meaning of its own: its axioms are a theory in matching logic, and the theory says which configurations a step can reach." },
        { hl: { a: [lineOf(sc, 'theorem sound_and_complete')] }, notes: [note('a', lineOf(sc, 'theorem sound_and_complete'), 'Stated, not proved yet.', 'sorry')], say: '`sound_and_complete` states that the two agree, for every well-formed definition whose ==obligations== hold.' },
        { hl: { a: [lineOf(sc, 'wf d = true → Obligations d →')] }, notes: [note('a', lineOf(sc, 'wf d = true → Obligations d →'), "What `wf` can't decide: that some functions terminate, or that a `[total]` one always has a value.", 'Obligations d')], say: "peano has no obligations: its generated `Tie/Wf.lean` proves the lists are empty." },
        { say: "Until it is proved, a theorem about `Step` is a theorem about peano's KORE as KCore reads it. Lesson 3 shows that reading, so you can judge it yourself." },
      ],
    },
  ],
  quiz: [
    {
      q: 'What makes the definition in the Lean package peano, and not some other definition?',
      options: ["The generator's parser is reviewed", 'The tie: the kernel checked that the term is the parse of the KORE text, is well formed, and prints back as that text up to the order of sentences', '`names_ok`'],
      answer: 1,
      why: '`Peano.tied` is the kernel-checked link; `names_ok` only checks the readable names.',
    },
    {
      q: 'Why can the comparison ignore the order of sentences?',
      options: ['Because kompile always writes them in the same order', 'Because a KORE module states a set of axioms, so the order carries no meaning', 'It cannot; it is an approximation'],
      answer: 1,
      why: 'The same point as lesson 1: axioms have no order.',
    },
    {
      q: 'In the term, how does a step tell `s` from `z`?',
      options: ['By comparing their names', 'By comparing their numbers', 'By their position in the KORE file'],
      answer: 1,
      why: 'Names are for printing. Everything that steps or decides compares numbers.',
    },
  ],
  checked: [
    "`Peano.tied`, by the kernel: the package's term is KCore's `parse` of peano's KORE, it is well formed, and its `emit` is that KORE up to the order of sentences. Its proof uses only `propext`, `Classical.choice` and `Quot.sound`.",
    '`rule0`, `rule1`, `fn_pred_sig`, `fn_pred_0` and `names_ok`, by the kernel: the readable forms of the term in these scenes.',
    `The well-formedness report and the cost table are the compiled \`wf\` and the package build's measurements (one thread; peak memory of the process). The tie is ${pkg.tie.length} modules, ${seconds(pkg.tie).toFixed(0)} s in all.`,
    "Not checked: that kompile's KORE means what `peano.k` means, and that `Step` is what the KORE means (`sound_and_complete`, stated with `sorry`).",
    `Trusted: the reader that turns the KORE file's text into its syntax tree, the Lean term \`kore\` (\`kore_term\`). The tie starts from that tree: ${fmt(emit.modules.reduce((sum, m) => sum + m.sentences, 0))} sentences in ${emit.modules.length} modules.`,
  ],
  tryit: [
    {
      say: 'In the kcore-spec package directory, with the library built (`lake build KcoreSpec kcore`):',
      cmd: 'gen/gen.sh ../milestone-1/kore/definition.kore examples/peano Peano   # writes the package\ngen/build.sh --tie examples/peano                                    # builds it, with the tie',
    },
  ],
}
