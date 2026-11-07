'use client'

// Lesson "The definition as a Lean value": the three parts of `Definition`, the generator `emit`,
// the fragment F0 and its round trip, and what F0 rejects. Counts of the emitted KORE and the
// well-formedness report were computed by Lean on peano's data (Facts.lean); the rejection
// mechanisms are the build's own checked output (SpecChecks.lean); the kernel costs are the last
// run of test/F0Check.lean.

import { fmt, lean, lineOf, source, span } from './data'
import { LessonScene, type Step } from './LessonScene'

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

// ---- 1. Three parts ------------------------------------------------------------------------------

export function PartsScene() {
  const steps: Step[] = [
    { say: <>A definition is a Lean value of type <code>Definition</code>, with three fields.</>, hl: { d: span(defs, 'structure Definition where', 'cert : Certificates') }, panes: ['d'] },
    { say: <>The core is what a step reads: sorts, constructors, functions with their clauses, subsorts, the sort of the program, and the rules. Lesson 4 reads it.</>, hl: { c: span(core, 'def peanoCore : Semantics', 'rhs := tcfg (tdone') }, panes: ['d', 'c'] },
    { say: <>The presentation is what kompile wrote that a generator cannot recompute: source locations, content hashes, the names of variables kompile invented, the order in which productions appeared.</>, hl: { d: span(defs, 'structure Presentation where', 'initUid : String'), p: span(pres, 'def peanoPres : Presentation', 'initUid :=') }, panes: ['d', 'p'] },
    { say: <>For peano it holds, for example, <code>_Gen4</code> and <code>_DotVar0</code>, the names kompile gave the shared subterm and the counter cell in the first rule.</>, hl: { p: [lineOf(pres, `names := ["N", "'Unds'Gen4", "'Unds'DotVar0"]`)] }, panes: ['p'] },
    { say: <>The certificate says, for each function, on which argument its recursive calls decrease. <code>pred</code> makes none, so peano's certificate is <code>[none]</code>.</>, hl: { d: span(defs, 'structure Certificates where', 'decreasing : List (Option Nat)'), p: [lineOf(pres, 'def peano : Definition')] }, panes: ['d', 'p'] },
  ]
  return (
    <LessonScene
      title="A definition has three parts"
      panes={[
        { id: 'd', label: 'The type', source: defs },
        { id: 'c', label: "peano's core", source: core },
        { id: 'p', label: "peano's presentation and the definition", source: pres },
      ]}
      steps={steps}
      questions={[
        { q: 'Why keep hashes and source locations at all, if no step reads them?',
          a: <>To reproduce kompile's KORE exactly. The check of scene 3 compares the generated KORE with kompile's, and the comparison does no renaming or normalization.</> },
        { q: <>Can the presentation change what a statement about <code>Step</code> means?</>,
          a: <>No: <code>Step</code> takes the core only. The theory Γ_D is translated from the whole KORE text, so it reads the presentation; that it does not depend on it is stated in the package, not yet proved.</> },
      ]}
    />
  )
}

// ---- 2. emit -------------------------------------------------------------------------------------

export function EmitScene() {
  const kinds = stats.userKinds
  if (stats.emptySlices.length) throw new Error(`lean lessons: empty fixed slices ${stats.emptySlices.join(', ')}`)
  const steps: Step[] = [
    { say: <><code>emit</code> writes the KORE of a definition from its core and its presentation. It never reads the certificate.</>, hl: { h: span(emitHead, '`emit : Semantics → Presentation', 'the certificate is not emitted.') }, panes: ['h'] },
    { say: <>It writes the user module in kompile's order: sort declarations, symbol declarations, the axioms kompile derives from declarations, then equations and rules, then helper equations.</>, hl: { u: span(user, 'sentences :=', '++ fixedSentences "F0-MAP-CEIL"') }, panes: ['u'] },
    { say: <>Where the text is the same for every definition, <code>emit</code> copies it: each <code>fixedSentences</code> line is a slice of fixed KORE, cut from kompile's output once.</>, hl: { u: user.text.split('\n').map((row, i) => (row.includes('fixedSentences') ? user.start + i : -1)).filter((l) => l > 0) }, panes: ['u'] },
    { say: <>Everything else comes from a field of the core: one symbol per constructor, an equation per clause, an axiom per rule.</>, hl: { u: [lineOf(user, '++ (prods c p).flatMap (prodSymbol p)'), lineOf(user, '++ (withPres c.fns p.fns).flatMap'), lineOf(user, '++ (rulesWith c p).map')] }, panes: ['u'] },
    { say: <>For peano, <code>emit</code> writes {stats.modules.length} modules. The user module has {fmt(stats.modules[stats.modules.length - 1].sentences)} sentences: {fmt(kinds.sort ?? 0)} sort declarations, {fmt(kinds.symbol ?? 0)} symbol declarations and {fmt(kinds.axiom ?? 0)} axioms. {fmt(stats.fixedInUser)} of them are fixed text.</>, panes: ['u'] },
  ]
  return (
    <LessonScene
      title="emit: from the value back to KORE"
      panes={[
        { id: 'h', label: 'What emit is', source: emitHead },
        { id: 'u', label: 'The user module it writes', source: user },
      ]}
      steps={steps}
      questions={[
        { q: <>Why is it <code>emit</code>, from Lean to KORE, that has to be reviewed, and not a reader from KORE to Lean?</>,
          a: <>Scene 3: a reader's output is checked by running <code>emit</code> on it and comparing with the input. Only the direction that is compared against has to be right.</> },
        { q: <>If <code>emit</code> wrote a rule's axiom wrongly, what would happen with peano?</>,
          a: <>The KORE it writes would differ from kompile's, the comparison of scene 3 would fail, and peano would not be accepted. A wrong <code>emit</code> could only make a correct definition fail, unless it were wrong in exactly the way kompile is.</> },
      ]}
    />
  )
}

// ---- 3. The round trip and F0 ----------------------------------------------------------------------

export function RoundTripScene() {
  const d = lean.f0check.decisions
  const steps: Step[] = [
    { say: <>A KORE text <code>k</code> is in the fragment F0 when a reader finds a definition <code>d</code> in it, <code>d</code> is well formed, and <code>emit d</code> is <code>k</code> up to the order of each module's sentences.</>, hl: { f: span(fragment, 'def F0 (k : Kore.Definition) : Prop :=', '| none => False') }, panes: ['f'] },
    { say: <>The reader, <code>parse</code>, is not reviewed. Whatever it returns is checked by the other two conditions, so a wrong reader can only reject.</>, hl: { r: span(parseHead, '`parse : Kore.Definition', 'k is rejected.') }, panes: ['f', 'r'] },
    { say: <><code>F0.sound</code> is what a reader of the statements relies on: a text in F0 is the emitted KORE of a well-formed definition. Its proof is a case split on what the reader returned.</>, hl: { f: span(fragment, 'theorem F0.sound', '· exact h.elim') }, panes: ['f'] },
    { say: <>"Up to order" is <code>Reordered</code>: the same modules, names and attributes, and in each module the same sentences, counted with repetitions, in any order.</>, hl: { f: span(fragment, 'def Reordered (e k : Kore.Definition) : Prop :=', 'mm.1.sentences.Perm mm.2.sentences') }, panes: ['f'] },
    { say: <>The order of sentences has no meaning in KORE, and the package proves the part that matters: the theories of two reordered texts have the same models.</>, hl: { o: span(reorder, 'theorem reordered_sameModels', 'SameModels (Theory.ofDefinition d.emit)') }, panes: ['f', 'o'] },
    { say: <><code>wf</code> is eight conditions on the definition. For peano Lean computes all eight true.</>, hl: { f: span(fragment, 'def Definition.report', '("presentation: variable names distinct", d.pres.ok d.sem)]') }, panes: ['f'] },
    { say: <>For peano the kernel checks more than F0 needs: <code>emit peano</code> equals kompile's KORE exactly, in the same order. In the last run the three checks cost {fmt(d.wf_peano.kHb)}, {fmt(d.emit_peano.kHb)} and {fmt(d.peano_F0.kHb)} thousand heartbeats, {d.wf_peano.seconds}, {d.emit_peano.seconds} and {d.peano_F0.seconds} seconds.</>, hl: { k: span(f0, 'theorem wf_peano', 'theorem peano_F0') }, panes: ['k'] },
  ]
  if (!stats.report.every((r) => r.holds) || !stats.wf) throw new Error('lean lessons: peano is no longer well formed')
  return (
    <LessonScene
      title="The round trip: F0"
      panes={[
        { id: 'f', label: 'The fragment F0', source: fragment },
        { id: 'r', label: 'The reader', source: parseHead },
        { id: 'o', label: 'Order has no meaning', source: reorder },
        { id: 'k', label: 'Kernel checks for peano', source: f0 },
      ]}
      steps={steps}
      questions={[
        { q: <>Which of the three conditions of F0 would catch a reader that dropped one of peano's rules?</>,
          a: <>The comparison: <code>emit</code> of the definition with one rule writes one rule axiom, and kompile's text has two.</> },
        { q: 'Why is comparing up to order enough, when exact equality was possible for peano?',
          a: <>krust writes some sentences in an order that depends on module names. Exact equality would reject those definitions for a reason that changes no axiom; <code>reordered_sameModels</code> shows the looser comparison loses nothing.</> },
      ]}
    />
  )
}

// ---- 4. What F0 rejects ----------------------------------------------------------------------------

export function RejectScene() {
  const f = lean.f0check
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
  const steps: Step[] = [
    { say: <>The package keeps a list of KORE texts that F0 must reject: mutations of peano's KORE, and the counterexamples two reviews of earlier versions found. The build checks the reason each one is rejected.</>, hl: { w: block('info: [("m1 drop') }, panes: ['w'] },
    { say: <>Dropping an equation, or adding an <code>owise</code> attribute to a rule, changes the text: some sentence of it is not one <code>emit</code> writes.</>, hl: { w: [lineOf(diag, '("m1 drop'), lineOf(diag, '("m4 owise')] }, panes: ['w'] },
    { say: <>A second equation that overlaps the first is rejected by <code>wf</code>: functions must be deterministic.</>, hl: { w: [lineOf(diag, '("m2 second')] }, panes: ['w'] },
    { say: <>A recursive call that does not decrease is rejected by <code>wf</code> through the certificate.</>, hl: { w: [lineOf(diag, '("m3 pred'), lineOf(diag, '("R1-3 decreasing')] }, panes: ['w'] },
    { say: <>Axioms that would make the theory say something false, such as <code>⊤Bool = ⊥Bool</code>, are rejected because <code>emit</code> never writes them.</>, hl: { w: [lineOf(diag, '("R1-6c [assoc]'), lineOf(diag, '("R1-6b [functional]')] }, panes: ['w'] },
    { say: <>Each rejection, and three repaired versions that F0 accepts, is also a theorem the kernel checked: {f.rejections} rejections and {f.controls} acceptances, {fmt(f.rejectionKHb)} thousand heartbeats in all.</>, hl: { k: span(f0, 'theorem m1_not_F0', 'theorem w5ok_F0') }, panes: ['k'] },
  ]
  return (
    <LessonScene
      title="What F0 rejects"
      panes={[
        { id: 'w', label: 'Why each is rejected (checked by the build)', source: diag },
        { id: 'k', label: 'The same, as kernel theorems', source: f0 },
      ]}
      steps={steps}
      questions={[
        { q: 'Why are most rejections "not emitted" rather than a specific error?',
          a: <>F0 does not look for bad shapes. It accepts exactly what <code>emit</code> writes for well-formed data, so anything else, whatever is wrong with it, is some sentence <code>emit</code> does not write.</> },
        { q: 'What would it take to make F0 accept a wrong axiom?',
          a: <>A well-formed definition whose <code>emit</code> writes it. That is a question about <code>emit</code>'s text, read once for every definition; lesson 6 counts its lines.</> },
      ]}
    />
  )
}
